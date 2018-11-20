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
               (fun uu___356_367  ->
                  match uu___356_367 with
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
  fun uu___357_651  ->
    match uu___357_651 with
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
        let uu___361_3813 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___361_3813.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___361_3813.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___361_3813.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___361_3813.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___361_3813.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___361_3813.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___361_3813.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___361_3813.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___361_3813.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___361_3813.FStar_SMTEncoding_Env.current_module_name);
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
           (t1,FStar_Syntax_Syntax.Meta_short_circuit ) ->
           ((let uu____4244 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.print2
               "\nTerm %s:%s has been checked with short circuit semantics, but is deep embedded to smt\n"
               ((env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.curmodule).FStar_Ident.str
               uu____4244);
            encode_term t1 env)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4248) ->
           encode_term t1
             (let uu___362_4266 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___362_4266.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___362_4266.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___362_4266.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___362_4266.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___362_4266.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___362_4266.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___362_4266.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___362_4266.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___362_4266.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___362_4266.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4269) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4277 = head_redex env t  in
           if uu____4277
           then let uu____4284 = whnf env t  in encode_term uu____4284 env
           else
             (let uu____4287 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4287 with
              | (uu____4298,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____4308 ->
                          let uu____4314 =
                            let uu____4315 =
                              let uu____4323 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4324 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4323,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4324)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4315  in
                          [uu____4314]
                      | FStar_SMTEncoding_Term.App (uu____4330,[]) ->
                          let uu____4333 =
                            let uu____4334 =
                              let uu____4342 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4343 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4342,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4343)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4334  in
                          [uu____4333]
                      | uu____4349 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4352 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4354) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4384 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4384 with
            | (binders1,res) ->
                let uu____4395 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4395
                then
                  let uu____4402 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4402 with
                   | (vars,guards,env',decls,uu____4427) ->
                       let fsym =
                         let uu____4446 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4446, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4452 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___363_4461 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___363_4461.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___363_4461.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___363_4461.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___363_4461.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___363_4461.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___363_4461.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___363_4461.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___363_4461.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___363_4461.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___363_4461.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___363_4461.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___363_4461.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___363_4461.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___363_4461.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___363_4461.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___363_4461.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___363_4461.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___363_4461.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___363_4461.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___363_4461.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___363_4461.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___363_4461.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___363_4461.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___363_4461.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___363_4461.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___363_4461.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___363_4461.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___363_4461.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___363_4461.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___363_4461.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___363_4461.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___363_4461.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___363_4461.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___363_4461.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___363_4461.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___363_4461.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___363_4461.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___363_4461.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___363_4461.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___363_4461.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___363_4461.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___363_4461.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4452 with
                        | (pre_opt,res_t) ->
                            let uu____4473 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4473 with
                             | (res_pred,decls') ->
                                 let uu____4484 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4497 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4497, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4501 =
                                         encode_formula pre env'  in
                                       (match uu____4501 with
                                        | (guard,decls0) ->
                                            let uu____4514 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4514, decls0))
                                    in
                                 (match uu____4484 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4528 =
                                          let uu____4539 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4539)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4528
                                         in
                                      let cvars =
                                        let uu____4556 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4556
                                          (FStar_List.filter
                                             (fun uu____4586  ->
                                                match uu____4586 with
                                                | (x,uu____4594) ->
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
                                      let uu____4613 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4613 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4621 =
                                             let uu____4622 =
                                               let uu____4630 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4630)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4622
                                              in
                                           (uu____4621,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4652 =
                                               let uu____4654 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4654
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4652
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4667 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4667
                                             then
                                               let uu____4670 =
                                                 let uu____4672 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4672 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4670
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
                                             let uu____4685 =
                                               let uu____4693 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4693)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4685
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
                                             let uu____4709 =
                                               let uu____4717 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4717,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4709
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
                                             let uu____4734 =
                                               let uu____4742 =
                                                 let uu____4743 =
                                                   let uu____4754 =
                                                     let uu____4755 =
                                                       let uu____4760 =
                                                         let uu____4761 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4761
                                                          in
                                                       (f_has_t, uu____4760)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4755
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4754)
                                                    in
                                                 let uu____4776 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4776 uu____4743  in
                                               (uu____4742,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4734
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4799 =
                                               let uu____4807 =
                                                 let uu____4808 =
                                                   let uu____4819 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4819)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4808
                                                  in
                                               (uu____4807,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4799
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
                                           ((let uu____4840 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4840);
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
                     let uu____4859 =
                       let uu____4867 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4867,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4859  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4886 =
                       let uu____4894 =
                         let uu____4895 =
                           let uu____4906 =
                             let uu____4907 =
                               let uu____4912 =
                                 let uu____4913 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4913
                                  in
                               (f_has_t, uu____4912)  in
                             FStar_SMTEncoding_Util.mkImp uu____4907  in
                           ([[f_has_t]], [fsym], uu____4906)  in
                         let uu____4933 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4933 uu____4895  in
                       (uu____4894, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4886  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4951 ->
           let uu____4958 =
             let uu____4963 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4963 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4970;
                 FStar_Syntax_Syntax.vars = uu____4971;_} ->
                 let uu____4978 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4978 with
                  | (b,f1) ->
                      let uu____5003 =
                        let uu____5004 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5004  in
                      (uu____5003, f1))
             | uu____5019 -> failwith "impossible"  in
           (match uu____4958 with
            | (x,f) ->
                let uu____5031 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5031 with
                 | (base_t,decls) ->
                     let uu____5042 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5042 with
                      | (x1,xtm,env') ->
                          let uu____5059 = encode_formula f env'  in
                          (match uu____5059 with
                           | (refinement,decls') ->
                               let uu____5070 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5070 with
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
                                      let uu____5095 =
                                        let uu____5103 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5111 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5103
                                          uu____5111
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5095
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5159  ->
                                              match uu____5159 with
                                              | (y,uu____5167) ->
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
                                    let uu____5205 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5205 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5213 =
                                           let uu____5214 =
                                             let uu____5222 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5222)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5214
                                            in
                                         (uu____5213,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5246 =
                                             let uu____5248 =
                                               let uu____5250 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5250
                                                in
                                             Prims.strcat module_name
                                               uu____5248
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5246
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
                                           let uu____5268 =
                                             let uu____5276 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5276)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5268
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
                                           let uu____5293 =
                                             let uu____5301 =
                                               let uu____5302 =
                                                 let uu____5313 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5313)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5302
                                                in
                                             (uu____5301,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5293
                                            in
                                         let t_kinding =
                                           let uu____5327 =
                                             let uu____5335 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5335,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5327
                                            in
                                         let t_interp =
                                           let uu____5349 =
                                             let uu____5357 =
                                               let uu____5358 =
                                                 let uu____5369 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5369)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5358
                                                in
                                             (uu____5357,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5349
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5396 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5396);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5398) ->
           let ttm =
             let uu____5416 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5416  in
           let uu____5418 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5418 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5430 =
                    let uu____5438 =
                      let uu____5440 =
                        let uu____5442 =
                          let uu____5444 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5444  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5442  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5440
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5438)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5430  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5450 ->
           let uu____5467 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5467 with
            | (head1,args_e) ->
                let uu____5514 =
                  let uu____5529 =
                    let uu____5530 = FStar_Syntax_Subst.compress head1  in
                    uu____5530.FStar_Syntax_Syntax.n  in
                  (uu____5529, args_e)  in
                (match uu____5514 with
                 | uu____5547 when head_redex env head1 ->
                     let uu____5562 = whnf env t  in
                     encode_term uu____5562 env
                 | uu____5563 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5586 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5604) when
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
                       FStar_Syntax_Syntax.pos = uu____5626;
                       FStar_Syntax_Syntax.vars = uu____5627;_},uu____5628),uu____5629)
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
                       FStar_Syntax_Syntax.pos = uu____5655;
                       FStar_Syntax_Syntax.vars = uu____5656;_},uu____5657),
                    (v0,uu____5659)::(v1,uu____5661)::(v2,uu____5663)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5734 = encode_term v0 env  in
                     (match uu____5734 with
                      | (v01,decls0) ->
                          let uu____5745 = encode_term v1 env  in
                          (match uu____5745 with
                           | (v11,decls1) ->
                               let uu____5756 = encode_term v2 env  in
                               (match uu____5756 with
                                | (v21,decls2) ->
                                    let uu____5767 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5767,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5770)::(v1,uu____5772)::(v2,uu____5774)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5841 = encode_term v0 env  in
                     (match uu____5841 with
                      | (v01,decls0) ->
                          let uu____5852 = encode_term v1 env  in
                          (match uu____5852 with
                           | (v11,decls1) ->
                               let uu____5863 = encode_term v2 env  in
                               (match uu____5863 with
                                | (v21,decls2) ->
                                    let uu____5874 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5874,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5876)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5912)::(rng,uu____5914)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5965) ->
                     let e0 =
                       let uu____5987 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5987
                        in
                     ((let uu____5997 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5997
                       then
                         let uu____6002 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6002
                       else ());
                      (let e =
                         let uu____6010 =
                           let uu____6015 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6016 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6015
                             uu____6016
                            in
                         uu____6010 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6027),(arg,uu____6029)::[]) -> encode_term arg env
                 | uu____6064 ->
                     let uu____6079 = encode_args args_e env  in
                     (match uu____6079 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6140 = encode_term head1 env  in
                            match uu____6140 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6212 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6212 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6310  ->
                                                 fun uu____6311  ->
                                                   match (uu____6310,
                                                           uu____6311)
                                                   with
                                                   | ((bv,uu____6341),
                                                      (a,uu____6343)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6373 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6373
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6374 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6374 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6389 =
                                                   let uu____6397 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6406 =
                                                     let uu____6408 =
                                                       let uu____6410 =
                                                         let uu____6412 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6412
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6410
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6408
                                                      in
                                                   (uu____6397,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6406)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6389
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6434 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6434 with
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
                                   FStar_Syntax_Syntax.pos = uu____6465;
                                   FStar_Syntax_Syntax.vars = uu____6466;_},uu____6467)
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
                                   FStar_Syntax_Syntax.pos = uu____6474;
                                   FStar_Syntax_Syntax.vars = uu____6475;_},uu____6476)
                                ->
                                let uu____6481 =
                                  let uu____6482 =
                                    let uu____6487 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6487
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6482
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6481
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6517 =
                                  let uu____6518 =
                                    let uu____6523 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6523
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6518
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6517
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6552,(FStar_Util.Inl t1,uu____6554),uu____6555)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6602,(FStar_Util.Inr c,uu____6604),uu____6605)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6652 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6673 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6673
                                  in
                               let uu____6674 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6674 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6690;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6691;_},uu____6692)
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
                                     | uu____6710 ->
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
           let uu____6789 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6789 with
            | (bs1,body1,opening) ->
                let fallback uu____6814 =
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
                  let uu____6824 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6824, [decl])  in
                let is_impure rc =
                  let uu____6835 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6835 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6850 =
                          let uu____6863 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6863
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6850 with
                         | (t1,uu____6866,uu____6867) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6885 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6885
                  then
                    let uu____6890 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6890
                  else
                    (let uu____6893 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6893
                     then
                       let uu____6898 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6898
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6906 =
                         let uu____6912 =
                           let uu____6914 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6914
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6912)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6906);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6919 =
                       (is_impure rc) &&
                         (let uu____6922 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6922)
                        in
                     if uu____6919
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6933 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6933 with
                        | (vars,guards,envbody,decls,uu____6958) ->
                            let body2 =
                              let uu____6972 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6972
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6977 = encode_term body2 envbody  in
                            (match uu____6977 with
                             | (body3,decls') ->
                                 let uu____6988 =
                                   let uu____6997 = codomain_eff rc  in
                                   match uu____6997 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7016 = encode_term tfun env
                                          in
                                       (match uu____7016 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6988 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7050 =
                                          let uu____7061 =
                                            let uu____7062 =
                                              let uu____7067 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7067, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7062
                                             in
                                          ([], vars, uu____7061)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7050
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
                                            let uu____7091 =
                                              let uu____7099 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____7099
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____7091
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
                                      let uu____7126 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____7126 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____7134 =
                                             let uu____7135 =
                                               let uu____7143 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____7143)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7135
                                              in
                                           (uu____7134,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____7154 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7154 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____7163 =
                                                    let uu____7165 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____7165 = cache_size
                                                     in
                                                  if uu____7163
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
                                                    let uu____7186 =
                                                      let uu____7188 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____7188
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____7186
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
                                                  let uu____7198 =
                                                    let uu____7206 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7206)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7198
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
                                                      let uu____7228 =
                                                        let uu____7229 =
                                                          let uu____7237 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7237,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7229
                                                         in
                                                      [uu____7228]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7252 =
                                                    let uu____7260 =
                                                      let uu____7261 =
                                                        let uu____7272 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7272)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7261
                                                       in
                                                    (uu____7260,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7252
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
                                                ((let uu____7287 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____7287);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7288,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7289;
                          FStar_Syntax_Syntax.lbunivs = uu____7290;
                          FStar_Syntax_Syntax.lbtyp = uu____7291;
                          FStar_Syntax_Syntax.lbeff = uu____7292;
                          FStar_Syntax_Syntax.lbdef = uu____7293;
                          FStar_Syntax_Syntax.lbattrs = uu____7294;
                          FStar_Syntax_Syntax.lbpos = uu____7295;_}::uu____7296),uu____7297)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7331;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7333;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7335;
                FStar_Syntax_Syntax.lbpos = uu____7336;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7363 ->
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
              let uu____7435 =
                let uu____7440 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7440 env  in
              match uu____7435 with
              | (ee1,decls1) ->
                  let uu____7465 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7465 with
                   | (xs,e21) ->
                       let uu____7490 = FStar_List.hd xs  in
                       (match uu____7490 with
                        | (x1,uu____7508) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7514 = encode_body e21 env'  in
                            (match uu____7514 with
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
            let uu____7544 =
              let uu____7552 =
                let uu____7553 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7553  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7552  in
            match uu____7544 with
            | (scrsym,scr',env1) ->
                let uu____7563 = encode_term e env1  in
                (match uu____7563 with
                 | (scr,decls) ->
                     let uu____7574 =
                       let encode_branch b uu____7603 =
                         match uu____7603 with
                         | (else_case,decls1) ->
                             let uu____7622 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7622 with
                              | (p,w,br) ->
                                  let uu____7648 = encode_pat env1 p  in
                                  (match uu____7648 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7685  ->
                                                   match uu____7685 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7692 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7714 =
                                               encode_term w1 env2  in
                                             (match uu____7714 with
                                              | (w2,decls2) ->
                                                  let uu____7727 =
                                                    let uu____7728 =
                                                      let uu____7733 =
                                                        let uu____7734 =
                                                          let uu____7739 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7739)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7734
                                                         in
                                                      (guard, uu____7733)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7728
                                                     in
                                                  (uu____7727, decls2))
                                          in
                                       (match uu____7692 with
                                        | (guard1,decls2) ->
                                            let uu____7754 =
                                              encode_br br env2  in
                                            (match uu____7754 with
                                             | (br1,decls3) ->
                                                 let uu____7767 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7767,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7574 with
                      | (match_tm,decls1) ->
                          let uu____7788 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7788, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7811 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7811
       then
         let uu____7814 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7814
       else ());
      (let uu____7819 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7819 with
       | (vars,pat_term) ->
           let uu____7836 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7892  ->
                     fun v1  ->
                       match uu____7892 with
                       | (env1,vars1) ->
                           let uu____7948 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7948 with
                            | (xx,uu____7972,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7836 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8065 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8066 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8067 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8075 = encode_const c env1  in
                      (match uu____8075 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8083::uu____8084 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8088 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8111 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8111 with
                        | (uu____8119,uu____8120::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8125 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8161  ->
                                  match uu____8161 with
                                  | (arg,uu____8171) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8180 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8180))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8212) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8243 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8268 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8314  ->
                                  match uu____8314 with
                                  | (arg,uu____8330) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8339 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8339))
                         in
                      FStar_All.pipe_right uu____8268 FStar_List.flatten
                   in
                let pat_term1 uu____8370 = encode_term pat_term env1  in
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
      let uu____8380 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8428  ->
                fun uu____8429  ->
                  match (uu____8428, uu____8429) with
                  | ((tms,decls),(t,uu____8469)) ->
                      let uu____8496 = encode_term t env  in
                      (match uu____8496 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8380 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8553 = FStar_Syntax_Util.list_elements e  in
        match uu____8553 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8584 =
          let uu____8601 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8601 FStar_Syntax_Util.head_and_args  in
        match uu____8584 with
        | (head1,args) ->
            let uu____8652 =
              let uu____8667 =
                let uu____8668 = FStar_Syntax_Util.un_uinst head1  in
                uu____8668.FStar_Syntax_Syntax.n  in
              (uu____8667, args)  in
            (match uu____8652 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8690,uu____8691)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8743 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8798 =
            let uu____8815 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8815 FStar_Syntax_Util.head_and_args
             in
          match uu____8798 with
          | (head1,args) ->
              let uu____8862 =
                let uu____8877 =
                  let uu____8878 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8878.FStar_Syntax_Syntax.n  in
                (uu____8877, args)  in
              (match uu____8862 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8897)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8934 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8964 = smt_pat_or1 t1  in
            (match uu____8964 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8986 = list_elements1 e  in
                 FStar_All.pipe_right uu____8986
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9016 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9016
                           (FStar_List.map one_pat)))
             | uu____9039 ->
                 let uu____9044 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9044])
        | uu____9095 ->
            let uu____9098 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9098]
         in
      let uu____9149 =
        let uu____9164 =
          let uu____9165 = FStar_Syntax_Subst.compress t  in
          uu____9165.FStar_Syntax_Syntax.n  in
        match uu____9164 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9204 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9204 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9239;
                        FStar_Syntax_Syntax.effect_name = uu____9240;
                        FStar_Syntax_Syntax.result_typ = uu____9241;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9243)::(post,uu____9245)::(pats,uu____9247)::[];
                        FStar_Syntax_Syntax.flags = uu____9248;_}
                      ->
                      let uu____9309 = lemma_pats pats  in
                      (binders1, pre, post, uu____9309)
                  | uu____9320 -> failwith "impos"))
        | uu____9336 -> failwith "Impos"  in
      match uu____9149 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___364_9373 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___364_9373.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___364_9373.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___364_9373.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___364_9373.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___364_9373.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___364_9373.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___364_9373.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___364_9373.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___364_9373.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___364_9373.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9375 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9375 with
           | (vars,guards,env2,decls,uu____9400) ->
               let uu____9413 = encode_smt_patterns patterns env2  in
               (match uu____9413 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___365_9446 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___365_9446.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___365_9446.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___365_9446.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___365_9446.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___365_9446.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___365_9446.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___365_9446.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___365_9446.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___365_9446.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___365_9446.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9448 =
                      let uu____9453 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9453 env3  in
                    (match uu____9448 with
                     | (pre1,decls'') ->
                         let uu____9460 =
                           let uu____9465 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9465 env3  in
                         (match uu____9460 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9475 =
                                let uu____9476 =
                                  let uu____9487 =
                                    let uu____9488 =
                                      let uu____9493 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9493, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9488
                                     in
                                  (pats, vars, uu____9487)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9476
                                 in
                              (uu____9475, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___366_9515 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___366_9515.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___366_9515.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___366_9515.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___366_9515.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___366_9515.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___366_9515.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___366_9515.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___366_9515.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___366_9515.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___366_9515.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9531 = FStar_Syntax_Util.head_and_args t  in
        match uu____9531 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9594::(x,uu____9596)::(t1,uu____9598)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9665 = encode_term x env1  in
                 (match uu____9665 with
                  | (x1,decls) ->
                      let uu____9676 = encode_term t1 env1  in
                      (match uu____9676 with
                       | (t2,decls') ->
                           let uu____9687 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9687, (FStar_List.append decls decls'))))
             | uu____9688 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9731  ->
             match uu____9731 with
             | (pats_l1,decls) ->
                 let uu____9776 =
                   FStar_List.fold_right
                     (fun uu____9811  ->
                        fun uu____9812  ->
                          match (uu____9811, uu____9812) with
                          | ((p,uu____9854),(pats1,decls1)) ->
                              let uu____9889 = encode_smt_pattern p  in
                              (match uu____9889 with
                               | (t,d) ->
                                   let uu____9904 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9904 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9921 =
                                            let uu____9927 =
                                              let uu____9929 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9931 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9929 uu____9931
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9927)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9921);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9776 with
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
        let uu____9991 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9991
        then
          let uu____9996 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9998 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9996 uu____9998
        else ()  in
      let enc f r l =
        let uu____10040 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10072 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10072 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10040 with
        | (decls,args) ->
            let uu____10103 =
              let uu___367_10104 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___367_10104.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___367_10104.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10103, decls)
         in
      let const_op f r uu____10139 =
        let uu____10152 = f r  in (uu____10152, [])  in
      let un_op f l =
        let uu____10175 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10175  in
      let bin_op f uu___358_10195 =
        match uu___358_10195 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10206 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10247 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10272  ->
                 match uu____10272 with
                 | (t,uu____10288) ->
                     let uu____10293 = encode_formula t env  in
                     (match uu____10293 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10247 with
        | (decls,phis) ->
            let uu____10322 =
              let uu___368_10323 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___368_10323.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___368_10323.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10322, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10386  ->
               match uu____10386 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10407) -> false
                    | uu____10410 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10429 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10429
        else
          (let uu____10446 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10446 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10518 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10550 =
                       let uu____10555 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10556 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10555, uu____10556)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10550
                 | uu____10557 -> failwith "Impossible")
             in
          uu____10518 r args
        else
          (let uu____10563 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10563)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10635 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10667 =
                       let uu____10672 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10673 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10672, uu____10673)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10667
                 | uu____10674 -> failwith "Impossible")
             in
          uu____10635 r args
        else
          (let uu____10680 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10680)
         in
      let mk_imp1 r uu___359_10715 =
        match uu___359_10715 with
        | (lhs,uu____10721)::(rhs,uu____10723)::[] ->
            let uu____10764 = encode_formula rhs env  in
            (match uu____10764 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10779) ->
                      (l1, decls1)
                  | uu____10784 ->
                      let uu____10785 = encode_formula lhs env  in
                      (match uu____10785 with
                       | (l2,decls2) ->
                           let uu____10796 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10796, (FStar_List.append decls1 decls2)))))
        | uu____10797 -> failwith "impossible"  in
      let mk_ite r uu___360_10825 =
        match uu___360_10825 with
        | (guard,uu____10831)::(_then,uu____10833)::(_else,uu____10835)::[]
            ->
            let uu____10892 = encode_formula guard env  in
            (match uu____10892 with
             | (g,decls1) ->
                 let uu____10903 = encode_formula _then env  in
                 (match uu____10903 with
                  | (t,decls2) ->
                      let uu____10914 = encode_formula _else env  in
                      (match uu____10914 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10926 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10956 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10956  in
      let connectives =
        let uu____10986 =
          let uu____11011 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11011)  in
        let uu____11054 =
          let uu____11081 =
            let uu____11106 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11106)  in
          let uu____11149 =
            let uu____11176 =
              let uu____11203 =
                let uu____11228 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11228)  in
              let uu____11271 =
                let uu____11298 =
                  let uu____11325 =
                    let uu____11350 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11350)  in
                  [uu____11325;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11298  in
              uu____11203 :: uu____11271  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11176  in
          uu____11081 :: uu____11149  in
        uu____10986 :: uu____11054  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11895 = encode_formula phi' env  in
            (match uu____11895 with
             | (phi2,decls) ->
                 let uu____11906 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11906, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11908 ->
            let uu____11915 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11915 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11954 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11954 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11966;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11968;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11970;
                 FStar_Syntax_Syntax.lbpos = uu____11971;_}::[]),e2)
            ->
            let uu____11998 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11998 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12051::(x,uu____12053)::(t,uu____12055)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12122 = encode_term x env  in
                 (match uu____12122 with
                  | (x1,decls) ->
                      let uu____12133 = encode_term t env  in
                      (match uu____12133 with
                       | (t1,decls') ->
                           let uu____12144 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12144, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12147)::(msg,uu____12149)::(phi2,uu____12151)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12218 =
                   let uu____12223 =
                     let uu____12224 = FStar_Syntax_Subst.compress r  in
                     uu____12224.FStar_Syntax_Syntax.n  in
                   let uu____12227 =
                     let uu____12228 = FStar_Syntax_Subst.compress msg  in
                     uu____12228.FStar_Syntax_Syntax.n  in
                   (uu____12223, uu____12227)  in
                 (match uu____12218 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12237))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12248 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12255)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12290 when head_redex env head2 ->
                 let uu____12305 = whnf env phi1  in
                 encode_formula uu____12305 env
             | uu____12306 ->
                 let uu____12321 = encode_term phi1 env  in
                 (match uu____12321 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12333 =
                          let uu____12335 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12336 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12335 uu____12336
                           in
                        if uu____12333
                        then tt
                        else
                          (let uu___369_12340 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___369_12340.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___369_12340.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12341 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12341, decls)))
        | uu____12342 ->
            let uu____12343 = encode_term phi1 env  in
            (match uu____12343 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12355 =
                     let uu____12357 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12358 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12357 uu____12358  in
                   if uu____12355
                   then tt
                   else
                     (let uu___370_12362 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___370_12362.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___370_12362.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12363 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12363, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12407 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12407 with
        | (vars,guards,env2,decls,uu____12446) ->
            let uu____12459 = encode_smt_patterns ps env2  in
            (match uu____12459 with
             | (pats,decls') ->
                 let uu____12502 = encode_formula body env2  in
                 (match uu____12502 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12534;
                             FStar_SMTEncoding_Term.rng = uu____12535;_}::[])::[]
                            when
                            let uu____12552 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12552 = gf -> []
                        | uu____12555 -> guards  in
                      let uu____12560 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12560, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12571 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12571 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12580 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12686  ->
                     match uu____12686 with
                     | (l,uu____12711) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12580 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12780,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12872 = encode_q_body env vars pats body  in
             match uu____12872 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12917 =
                     let uu____12928 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12928)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12917
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12959 = encode_q_body env vars pats body  in
             match uu____12959 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13003 =
                   let uu____13004 =
                     let uu____13015 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13015)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13004
                    in
                 (uu____13003, decls))))
