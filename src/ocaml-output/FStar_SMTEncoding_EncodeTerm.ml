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
                  (let uu____625 = FStar_Util.first_N arity args  in
                   match uu____625 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____649 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____649 arity n_args rng)
  
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
          let uu____676 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____676 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___359_685  ->
    match uu___359_685 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____691 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____739;
                       FStar_SMTEncoding_Term.rng = uu____740;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____765) ->
              let uu____775 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____789 -> false) args (FStar_List.rev xs))
                 in
              if uu____775
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
                (fun uu____2144  ->
                   fun b  ->
                     match uu____2144 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2229 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2250 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2250 with
                           | (xxsym,xx,env') ->
                               let uu____2280 =
                                 let uu____2285 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2285 env1 xx
                                  in
                               (match uu____2280 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2229 with
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
          let uu____2459 = encode_term t env  in
          match uu____2459 with
          | (t1,decls) ->
              let uu____2470 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2470, decls)

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
          let uu____2481 = encode_term t env  in
          match uu____2481 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2496 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2496, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2498 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2498, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2504 = encode_args args_e env  in
        match uu____2504 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2523 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2535 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2535  in
            let binary arg_tms1 =
              let uu____2550 =
                let uu____2551 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2551  in
              let uu____2552 =
                let uu____2553 =
                  let uu____2554 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2554  in
                FStar_SMTEncoding_Term.unboxInt uu____2553  in
              (uu____2550, uu____2552)  in
            let mk_default uu____2562 =
              let uu____2563 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2563 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2640 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2640
              then
                let uu____2643 =
                  let uu____2644 = mk_args ts  in op uu____2644  in
                FStar_All.pipe_right uu____2643 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2682 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2682
              then
                let uu____2685 = binary ts  in
                match uu____2685 with
                | (t1,t2) ->
                    let uu____2692 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2692
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2698 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2698
                 then
                   let uu____2701 =
                     let uu____2702 = binary ts  in op uu____2702  in
                   FStar_All.pipe_right uu____2701
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
            let uu____2867 =
              let uu____2877 =
                FStar_List.tryFind
                  (fun uu____2901  ->
                     match uu____2901 with
                     | (l,uu____2912) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2877 FStar_Util.must  in
            (match uu____2867 with
             | (uu____2956,op) ->
                 let uu____2968 = op arg_tms  in (uu____2968, decls))

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
        let uu____2976 = FStar_List.hd args_e  in
        match uu____2976 with
        | (tm_sz,uu____2984) ->
            let uu____2993 = uu____2976  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____3002 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____3002 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____3010 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____3010);
                   t_decls1)
               in
            let uu____3012 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3038::(sz_arg,uu____3040)::uu____3041::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3108 =
                    let uu____3109 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3109  in
                  let uu____3112 =
                    let uu____3116 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3116  in
                  (uu____3108, uu____3112)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3123::(sz_arg,uu____3125)::uu____3126::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3193 =
                    let uu____3195 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3195
                     in
                  failwith uu____3193
              | uu____3205 ->
                  let uu____3220 = FStar_List.tail args_e  in
                  (uu____3220, FStar_Pervasives_Native.None)
               in
            (match uu____3012 with
             | (arg_tms,ext_sz) ->
                 let uu____3239 = encode_args arg_tms env  in
                 (match uu____3239 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3260 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3272 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3272  in
                      let unary_arith arg_tms2 =
                        let uu____3283 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3283  in
                      let binary arg_tms2 =
                        let uu____3298 =
                          let uu____3299 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3299
                           in
                        let uu____3300 =
                          let uu____3301 =
                            let uu____3302 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3302  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3301
                           in
                        (uu____3298, uu____3300)  in
                      let binary_arith arg_tms2 =
                        let uu____3319 =
                          let uu____3320 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3320
                           in
                        let uu____3321 =
                          let uu____3322 =
                            let uu____3323 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3323  in
                          FStar_SMTEncoding_Term.unboxInt uu____3322  in
                        (uu____3319, uu____3321)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3381 =
                          let uu____3382 = mk_args ts  in op uu____3382  in
                        FStar_All.pipe_right uu____3381 resBox  in
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
                        let uu____3514 =
                          let uu____3519 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3519  in
                        let uu____3528 =
                          let uu____3533 =
                            let uu____3535 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3535  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3533  in
                        mk_bv uu____3514 unary uu____3528 arg_tms2  in
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
                      let uu____3775 =
                        let uu____3785 =
                          FStar_List.tryFind
                            (fun uu____3809  ->
                               match uu____3809 with
                               | (l,uu____3820) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3785 FStar_Util.must  in
                      (match uu____3775 with
                       | (uu____3866,op) ->
                           let uu____3878 = op arg_tms1  in
                           (uu____3878, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___363_3888 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___363_3888.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___363_3888.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___363_3888.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___363_3888.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___363_3888.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___363_3888.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___363_3888.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___363_3888.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___363_3888.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___363_3888.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3890 = encode_term t env1  in
      match uu____3890 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3912 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3912 with
           | FStar_Pervasives_Native.Some uu____3919 -> (tm, decls)
           | uu____3920 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3927,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3928;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3929;
                                  FStar_SMTEncoding_Term.rng = uu____3930;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3931;
                       FStar_SMTEncoding_Term.freevars = uu____3932;
                       FStar_SMTEncoding_Term.rng = uu____3933;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3967 ->
                    let uu____3968 = encode_formula t env1  in
                    (match uu____3968 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3985 =
                                 let uu____3990 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3990, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3985
                           | uu____3991 ->
                               let uu____3992 =
                                 let uu____4003 =
                                   let uu____4004 =
                                     let uu____4009 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____4009, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____4004
                                    in
                                 ([[valid_tm]], vars, uu____4003)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3992
                            in
                         let ax =
                           let uu____4019 =
                             let uu____4027 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____4027)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____4019  in
                         ((let uu____4034 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____4034);
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
      (let uu____4044 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4044
       then
         let uu____4049 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4051 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4053 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4049 uu____4051
           uu____4053
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4062 ->
           let uu____4085 =
             let uu____4087 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4090 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4092 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4094 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4087
               uu____4090 uu____4092 uu____4094
              in
           failwith uu____4085
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4101 =
             let uu____4103 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4106 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4108 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4110 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4103
               uu____4106 uu____4108 uu____4110
              in
           failwith uu____4101
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4120 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4120
             then
               let uu____4125 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4127 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4125
                 uu____4127
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4133 =
             let uu____4135 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4135
              in
           failwith uu____4133
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4144),uu____4145) ->
           let uu____4194 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4204 -> false  in
           if uu____4194
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4222) ->
           let tv =
             let uu____4228 =
               let uu____4235 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4235
                in
             uu____4228 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4262 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4262
             then
               let uu____4267 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4269 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4267
                 uu____4269
             else ());
            (let t1 =
               let uu____4277 =
                 let uu____4288 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4288]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4277
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4314) ->
           encode_term t1
             (let uu___364_4332 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___364_4332.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___364_4332.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___364_4332.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___364_4332.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___364_4332.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___364_4332.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___364_4332.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___364_4332.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___364_4332.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___364_4332.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4335) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4343 = head_redex env t  in
           if uu____4343
           then let uu____4350 = whnf env t  in encode_term uu____4350 env
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
                  | FStar_SMTEncoding_Term.FreeV uu____4358 ->
                      let uu____4364 =
                        let uu____4365 =
                          let uu____4373 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4374 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4373,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4374)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4365  in
                      [uu____4364]
                  | FStar_SMTEncoding_Term.App (uu____4380,[]) ->
                      let uu____4383 =
                        let uu____4384 =
                          let uu____4392 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4393 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4392,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4393)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4384  in
                      [uu____4383]
                  | uu____4399 -> []
                else []  in
              (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4402 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4404) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4434 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4434 with
            | (binders1,res) ->
                let uu____4445 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4445
                then
                  let uu____4452 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4452 with
                   | (vars,guards,env',decls,uu____4477) ->
                       let fsym =
                         let uu____4496 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4496, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4502 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___365_4511 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___365_4511.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___365_4511.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___365_4511.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___365_4511.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___365_4511.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___365_4511.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___365_4511.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___365_4511.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___365_4511.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___365_4511.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___365_4511.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___365_4511.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___365_4511.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___365_4511.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___365_4511.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___365_4511.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___365_4511.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___365_4511.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___365_4511.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___365_4511.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___365_4511.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___365_4511.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___365_4511.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___365_4511.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___365_4511.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___365_4511.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___365_4511.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___365_4511.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___365_4511.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___365_4511.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___365_4511.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___365_4511.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___365_4511.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___365_4511.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___365_4511.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___365_4511.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___365_4511.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___365_4511.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___365_4511.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___365_4511.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___365_4511.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___365_4511.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4502 with
                        | (pre_opt,res_t) ->
                            let uu____4523 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4523 with
                             | (res_pred,decls') ->
                                 let uu____4534 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4547 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4547, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4551 =
                                         encode_formula pre env'  in
                                       (match uu____4551 with
                                        | (guard,decls0) ->
                                            let uu____4564 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4564, decls0))
                                    in
                                 (match uu____4534 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4578 =
                                          let uu____4589 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4589)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4578
                                         in
                                      let cvars =
                                        let uu____4606 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4606
                                          (FStar_List.filter
                                             (fun uu____4636  ->
                                                match uu____4636 with
                                                | (x,uu____4644) ->
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
                                      let uu____4663 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4663 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4671 =
                                             let uu____4672 =
                                               let uu____4680 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4680)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4672
                                              in
                                           (uu____4671,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4702 =
                                               let uu____4704 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4704
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4702
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4717 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4717
                                             then
                                               let uu____4720 =
                                                 let uu____4722 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4722 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4720
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
                                             let uu____4735 =
                                               let uu____4743 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4743)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4735
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
                                             let uu____4759 =
                                               let uu____4767 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4767,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4759
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
                                             let uu____4784 =
                                               let uu____4792 =
                                                 let uu____4793 =
                                                   let uu____4804 =
                                                     let uu____4805 =
                                                       let uu____4810 =
                                                         let uu____4811 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4811
                                                          in
                                                       (f_has_t, uu____4810)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4805
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4804)
                                                    in
                                                 let uu____4826 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4826 uu____4793  in
                                               (uu____4792,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4784
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4849 =
                                               let uu____4857 =
                                                 let uu____4858 =
                                                   let uu____4869 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4869)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4858
                                                  in
                                               (uu____4857,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4849
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
                                           ((let uu____4890 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4890);
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
                     let uu____4909 =
                       let uu____4917 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4917,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4909  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4936 =
                       let uu____4944 =
                         let uu____4945 =
                           let uu____4956 =
                             let uu____4957 =
                               let uu____4962 =
                                 let uu____4963 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4963
                                  in
                               (f_has_t, uu____4962)  in
                             FStar_SMTEncoding_Util.mkImp uu____4957  in
                           ([[f_has_t]], [fsym], uu____4956)  in
                         let uu____4983 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4983 uu____4945  in
                       (uu____4944, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4936  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____5001 ->
           let uu____5008 =
             let uu____5013 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5013 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5020;
                 FStar_Syntax_Syntax.vars = uu____5021;_} ->
                 let uu____5028 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5028 with
                  | (b,f1) ->
                      let uu____5053 =
                        let uu____5054 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5054  in
                      (uu____5053, f1))
             | uu____5069 -> failwith "impossible"  in
           (match uu____5008 with
            | (x,f) ->
                let uu____5081 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5081 with
                 | (base_t,decls) ->
                     let uu____5092 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5092 with
                      | (x1,xtm,env') ->
                          let uu____5109 = encode_formula f env'  in
                          (match uu____5109 with
                           | (refinement,decls') ->
                               let uu____5120 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5120 with
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
                                      let uu____5145 =
                                        let uu____5153 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5161 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5153
                                          uu____5161
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5145
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5209  ->
                                              match uu____5209 with
                                              | (y,uu____5217) ->
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
                                    let uu____5255 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5255 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5263 =
                                           let uu____5264 =
                                             let uu____5272 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5272)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5264
                                            in
                                         (uu____5263,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5296 =
                                             let uu____5298 =
                                               let uu____5300 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5300
                                                in
                                             Prims.strcat module_name
                                               uu____5298
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5296
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
                                           let uu____5318 =
                                             let uu____5326 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5326)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5318
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
                                           let uu____5343 =
                                             let uu____5351 =
                                               let uu____5352 =
                                                 let uu____5363 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5363)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5352
                                                in
                                             (uu____5351,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5343
                                            in
                                         let t_kinding =
                                           let uu____5377 =
                                             let uu____5385 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5385,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5377
                                            in
                                         let t_interp =
                                           let uu____5399 =
                                             let uu____5407 =
                                               let uu____5408 =
                                                 let uu____5419 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5419)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5408
                                                in
                                             (uu____5407,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5399
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5446 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5446);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5448) ->
           let ttm =
             let uu____5466 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5466  in
           let uu____5468 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5468 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5480 =
                    let uu____5488 =
                      let uu____5490 =
                        let uu____5492 =
                          let uu____5494 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5494  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5492  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5490
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5488)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5480  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5500 ->
           let uu____5517 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5517 with
            | (head1,args_e) ->
                let uu____5564 =
                  let uu____5579 =
                    let uu____5580 = FStar_Syntax_Subst.compress head1  in
                    uu____5580.FStar_Syntax_Syntax.n  in
                  (uu____5579, args_e)  in
                (match uu____5564 with
                 | uu____5597 when head_redex env head1 ->
                     let uu____5612 = whnf env t  in
                     encode_term uu____5612 env
                 | uu____5613 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5636 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5654) when
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
                       FStar_Syntax_Syntax.pos = uu____5676;
                       FStar_Syntax_Syntax.vars = uu____5677;_},uu____5678),uu____5679)
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
                       FStar_Syntax_Syntax.pos = uu____5705;
                       FStar_Syntax_Syntax.vars = uu____5706;_},uu____5707),
                    (v0,uu____5709)::(v1,uu____5711)::(v2,uu____5713)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5784 = encode_term v0 env  in
                     (match uu____5784 with
                      | (v01,decls0) ->
                          let uu____5795 = encode_term v1 env  in
                          (match uu____5795 with
                           | (v11,decls1) ->
                               let uu____5806 = encode_term v2 env  in
                               (match uu____5806 with
                                | (v21,decls2) ->
                                    let uu____5817 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5817,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5820)::(v1,uu____5822)::(v2,uu____5824)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5891 = encode_term v0 env  in
                     (match uu____5891 with
                      | (v01,decls0) ->
                          let uu____5902 = encode_term v1 env  in
                          (match uu____5902 with
                           | (v11,decls1) ->
                               let uu____5913 = encode_term v2 env  in
                               (match uu____5913 with
                                | (v21,decls2) ->
                                    let uu____5924 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5924,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5926)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5962)::(rng,uu____5964)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6015) ->
                     let e0 =
                       let uu____6037 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6037
                        in
                     ((let uu____6047 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6047
                       then
                         let uu____6052 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6052
                       else ());
                      (let e =
                         let uu____6060 =
                           let uu____6065 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6066 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6065
                             uu____6066
                            in
                         uu____6060 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6077),(arg,uu____6079)::[]) -> encode_term arg env
                 | uu____6114 ->
                     let uu____6129 = encode_args args_e env  in
                     (match uu____6129 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6190 = encode_term head1 env  in
                            match uu____6190 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6262 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6262 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6360  ->
                                                 fun uu____6361  ->
                                                   match (uu____6360,
                                                           uu____6361)
                                                   with
                                                   | ((bv,uu____6391),
                                                      (a,uu____6393)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6423 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6423
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6424 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6424 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6439 =
                                                   let uu____6447 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6456 =
                                                     let uu____6458 =
                                                       let uu____6460 =
                                                         let uu____6462 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6462
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6460
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6458
                                                      in
                                                   (uu____6447,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6456)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6439
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6484 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6484 with
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
                                   FStar_Syntax_Syntax.pos = uu____6527;
                                   FStar_Syntax_Syntax.vars = uu____6528;_},uu____6529)
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
                                   FStar_Syntax_Syntax.pos = uu____6536;
                                   FStar_Syntax_Syntax.vars = uu____6537;_},uu____6538)
                                ->
                                let uu____6543 =
                                  let uu____6544 =
                                    let uu____6549 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6549
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6544
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6543
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6579 =
                                  let uu____6580 =
                                    let uu____6585 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6585
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6580
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6579
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6614,(FStar_Util.Inl t1,uu____6616),uu____6617)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6664,(FStar_Util.Inr c,uu____6666),uu____6667)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6714 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6735 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6735
                                  in
                               let uu____6736 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6736 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6752;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6753;_},uu____6754)
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
                                     | uu____6772 ->
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
           let uu____6851 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6851 with
            | (bs1,body1,opening) ->
                let fallback uu____6876 =
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
                  let uu____6886 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6886, [decl])  in
                let is_impure rc =
                  let uu____6897 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6897 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6912 =
                          let uu____6925 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6925
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6912 with
                         | (t1,uu____6928,uu____6929) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6947 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6947
                  then
                    let uu____6952 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6952
                  else
                    (let uu____6955 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6955
                     then
                       let uu____6960 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6960
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6968 =
                         let uu____6974 =
                           let uu____6976 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6976
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6974)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6968);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6981 =
                       (is_impure rc) &&
                         (let uu____6984 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6984)
                        in
                     if uu____6981
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6995 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6995 with
                        | (vars,guards,envbody,decls,uu____7020) ->
                            let body2 =
                              let uu____7034 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7034
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7039 = encode_term body2 envbody  in
                            (match uu____7039 with
                             | (body3,decls') ->
                                 let uu____7050 =
                                   let uu____7059 = codomain_eff rc  in
                                   match uu____7059 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7078 = encode_term tfun env
                                          in
                                       (match uu____7078 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7050 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7112 =
                                          let uu____7123 =
                                            let uu____7124 =
                                              let uu____7129 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7129, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7124
                                             in
                                          ([], vars, uu____7123)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7112
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7137 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7153 =
                                              let uu____7156 =
                                                let uu____7164 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7164
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7156
                                               in
                                            let uu____7182 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7153, uu____7182)
                                         in
                                      (match uu____7137 with
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
                                           let uu____7204 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7204 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7212 =
                                                  let uu____7213 =
                                                    let uu____7221 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7221)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7213
                                                   in
                                                (uu____7212,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (FStar_SMTEncoding_Env.use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7227 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7227 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7236 =
                                                         let uu____7238 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7238 =
                                                           cache_size
                                                          in
                                                       if uu____7236
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
                                                         let uu____7254 =
                                                           let uu____7256 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7256
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7254
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
                                                       let uu____7266 =
                                                         let uu____7274 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7274)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7266
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
                                                           let uu____7291 =
                                                             let uu____7292 =
                                                               let uu____7300
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7300,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7292
                                                              in
                                                           [uu____7291]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7315 =
                                                         let uu____7323 =
                                                           let uu____7324 =
                                                             let uu____7335 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7335)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7324
                                                            in
                                                         (uu____7323,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7315
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
                                                     ((let uu____7350 =
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7350);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7351,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7352;
                          FStar_Syntax_Syntax.lbunivs = uu____7353;
                          FStar_Syntax_Syntax.lbtyp = uu____7354;
                          FStar_Syntax_Syntax.lbeff = uu____7355;
                          FStar_Syntax_Syntax.lbdef = uu____7356;
                          FStar_Syntax_Syntax.lbattrs = uu____7357;
                          FStar_Syntax_Syntax.lbpos = uu____7358;_}::uu____7359),uu____7360)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7394;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7396;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7398;
                FStar_Syntax_Syntax.lbpos = uu____7399;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7426 ->
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
              let uu____7498 =
                let uu____7503 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7503 env  in
              match uu____7498 with
              | (ee1,decls1) ->
                  let uu____7528 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7528 with
                   | (xs,e21) ->
                       let uu____7553 = FStar_List.hd xs  in
                       (match uu____7553 with
                        | (x1,uu____7571) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7577 = encode_body e21 env'  in
                            (match uu____7577 with
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
            let uu____7607 =
              let uu____7615 =
                let uu____7616 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7616  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7615  in
            match uu____7607 with
            | (scrsym,scr',env1) ->
                let uu____7626 = encode_term e env1  in
                (match uu____7626 with
                 | (scr,decls) ->
                     let uu____7637 =
                       let encode_branch b uu____7666 =
                         match uu____7666 with
                         | (else_case,decls1) ->
                             let uu____7685 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7685 with
                              | (p,w,br) ->
                                  let uu____7711 = encode_pat env1 p  in
                                  (match uu____7711 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7748  ->
                                                   match uu____7748 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7755 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7777 =
                                               encode_term w1 env2  in
                                             (match uu____7777 with
                                              | (w2,decls2) ->
                                                  let uu____7790 =
                                                    let uu____7791 =
                                                      let uu____7796 =
                                                        let uu____7797 =
                                                          let uu____7802 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7802)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7797
                                                         in
                                                      (guard, uu____7796)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7791
                                                     in
                                                  (uu____7790, decls2))
                                          in
                                       (match uu____7755 with
                                        | (guard1,decls2) ->
                                            let uu____7817 =
                                              encode_br br env2  in
                                            (match uu____7817 with
                                             | (br1,decls3) ->
                                                 let uu____7830 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7830,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7637 with
                      | (match_tm,decls1) ->
                          let uu____7851 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7851, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7874 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7874
       then
         let uu____7877 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7877
       else ());
      (let uu____7882 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7882 with
       | (vars,pat_term) ->
           let uu____7899 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7955  ->
                     fun v1  ->
                       match uu____7955 with
                       | (env1,vars1) ->
                           let uu____8011 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8011 with
                            | (xx,uu____8035,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7899 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8128 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8129 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8130 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8138 = encode_const c env1  in
                      (match uu____8138 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8146::uu____8147 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8151 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8174 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8174 with
                        | (uu____8182,uu____8183::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8188 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8224  ->
                                  match uu____8224 with
                                  | (arg,uu____8234) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8243 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8243))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8275) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8306 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8331 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8377  ->
                                  match uu____8377 with
                                  | (arg,uu____8393) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8402 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8402))
                         in
                      FStar_All.pipe_right uu____8331 FStar_List.flatten
                   in
                let pat_term1 uu____8433 = encode_term pat_term env1  in
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
      let uu____8443 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8491  ->
                fun uu____8492  ->
                  match (uu____8491, uu____8492) with
                  | ((tms,decls),(t,uu____8532)) ->
                      let uu____8559 = encode_term t env  in
                      (match uu____8559 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8443 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8616 = FStar_Syntax_Util.list_elements e  in
        match uu____8616 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8647 =
          let uu____8664 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8664 FStar_Syntax_Util.head_and_args  in
        match uu____8647 with
        | (head1,args) ->
            let uu____8715 =
              let uu____8730 =
                let uu____8731 = FStar_Syntax_Util.un_uinst head1  in
                uu____8731.FStar_Syntax_Syntax.n  in
              (uu____8730, args)  in
            (match uu____8715 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8753,uu____8754)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8806 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8861 =
            let uu____8878 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8878 FStar_Syntax_Util.head_and_args
             in
          match uu____8861 with
          | (head1,args) ->
              let uu____8925 =
                let uu____8940 =
                  let uu____8941 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8941.FStar_Syntax_Syntax.n  in
                (uu____8940, args)  in
              (match uu____8925 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8960)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8997 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9027 = smt_pat_or1 t1  in
            (match uu____9027 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9049 = list_elements1 e  in
                 FStar_All.pipe_right uu____9049
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9079 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9079
                           (FStar_List.map one_pat)))
             | uu____9102 ->
                 let uu____9107 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9107])
        | uu____9158 ->
            let uu____9161 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9161]
         in
      let uu____9212 =
        let uu____9227 =
          let uu____9228 = FStar_Syntax_Subst.compress t  in
          uu____9228.FStar_Syntax_Syntax.n  in
        match uu____9227 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9267 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9267 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9302;
                        FStar_Syntax_Syntax.effect_name = uu____9303;
                        FStar_Syntax_Syntax.result_typ = uu____9304;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9306)::(post,uu____9308)::(pats,uu____9310)::[];
                        FStar_Syntax_Syntax.flags = uu____9311;_}
                      ->
                      let uu____9372 = lemma_pats pats  in
                      (binders1, pre, post, uu____9372)
                  | uu____9383 -> failwith "impos"))
        | uu____9399 -> failwith "Impos"  in
      match uu____9212 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___366_9436 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___366_9436.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___366_9436.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___366_9436.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___366_9436.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___366_9436.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___366_9436.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___366_9436.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___366_9436.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___366_9436.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___366_9436.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9438 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9438 with
           | (vars,guards,env2,decls,uu____9463) ->
               let uu____9476 = encode_smt_patterns patterns env2  in
               (match uu____9476 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___367_9509 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___367_9509.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___367_9509.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___367_9509.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___367_9509.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___367_9509.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___367_9509.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___367_9509.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___367_9509.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___367_9509.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___367_9509.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9511 =
                      let uu____9516 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9516 env3  in
                    (match uu____9511 with
                     | (pre1,decls'') ->
                         let uu____9523 =
                           let uu____9528 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9528 env3  in
                         (match uu____9523 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9538 =
                                let uu____9539 =
                                  let uu____9550 =
                                    let uu____9551 =
                                      let uu____9556 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9556, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9551
                                     in
                                  (pats, vars, uu____9550)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9539
                                 in
                              (uu____9538, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___368_9578 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___368_9578.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___368_9578.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___368_9578.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___368_9578.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___368_9578.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___368_9578.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___368_9578.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___368_9578.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___368_9578.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___368_9578.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9594 = FStar_Syntax_Util.head_and_args t  in
        match uu____9594 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9657::(x,uu____9659)::(t1,uu____9661)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9728 = encode_term x env1  in
                 (match uu____9728 with
                  | (x1,decls) ->
                      let uu____9739 = encode_term t1 env1  in
                      (match uu____9739 with
                       | (t2,decls') ->
                           let uu____9750 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9750, (FStar_List.append decls decls'))))
             | uu____9751 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9794  ->
             match uu____9794 with
             | (pats_l1,decls) ->
                 let uu____9839 =
                   FStar_List.fold_right
                     (fun uu____9874  ->
                        fun uu____9875  ->
                          match (uu____9874, uu____9875) with
                          | ((p,uu____9917),(pats1,decls1)) ->
                              let uu____9952 = encode_smt_pattern p  in
                              (match uu____9952 with
                               | (t,d) ->
                                   let uu____9967 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9967 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9984 =
                                            let uu____9990 =
                                              let uu____9992 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9994 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9992 uu____9994
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9990)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9984);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9839 with
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
        let uu____10054 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10054
        then
          let uu____10059 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10061 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10059 uu____10061
        else ()  in
      let enc f r l =
        let uu____10103 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10135 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10135 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10103 with
        | (decls,args) ->
            let uu____10166 =
              let uu___369_10167 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___369_10167.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___369_10167.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10166, decls)
         in
      let const_op f r uu____10202 =
        let uu____10215 = f r  in (uu____10215, [])  in
      let un_op f l =
        let uu____10238 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10238  in
      let bin_op f uu___360_10258 =
        match uu___360_10258 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10269 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10310 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10335  ->
                 match uu____10335 with
                 | (t,uu____10351) ->
                     let uu____10356 = encode_formula t env  in
                     (match uu____10356 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10310 with
        | (decls,phis) ->
            let uu____10385 =
              let uu___370_10386 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10386.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10386.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10385, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10449  ->
               match uu____10449 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10470) -> false
                    | uu____10473 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10492 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10492
        else
          (let uu____10509 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10509 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10581 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10613 =
                       let uu____10618 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10619 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10618, uu____10619)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10613
                 | uu____10620 -> failwith "Impossible")
             in
          uu____10581 r args
        else
          (let uu____10626 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10626)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10698 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10730 =
                       let uu____10735 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10736 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10735, uu____10736)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10730
                 | uu____10737 -> failwith "Impossible")
             in
          uu____10698 r args
        else
          (let uu____10743 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10743)
         in
      let mk_imp1 r uu___361_10778 =
        match uu___361_10778 with
        | (lhs,uu____10784)::(rhs,uu____10786)::[] ->
            let uu____10827 = encode_formula rhs env  in
            (match uu____10827 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10842) ->
                      (l1, decls1)
                  | uu____10847 ->
                      let uu____10848 = encode_formula lhs env  in
                      (match uu____10848 with
                       | (l2,decls2) ->
                           let uu____10859 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10859, (FStar_List.append decls1 decls2)))))
        | uu____10860 -> failwith "impossible"  in
      let mk_ite r uu___362_10888 =
        match uu___362_10888 with
        | (guard,uu____10894)::(_then,uu____10896)::(_else,uu____10898)::[]
            ->
            let uu____10955 = encode_formula guard env  in
            (match uu____10955 with
             | (g,decls1) ->
                 let uu____10966 = encode_formula _then env  in
                 (match uu____10966 with
                  | (t,decls2) ->
                      let uu____10977 = encode_formula _else env  in
                      (match uu____10977 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10989 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11019 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11019  in
      let connectives =
        let uu____11049 =
          let uu____11074 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11074)  in
        let uu____11117 =
          let uu____11144 =
            let uu____11169 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11169)  in
          let uu____11212 =
            let uu____11239 =
              let uu____11266 =
                let uu____11291 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11291)  in
              let uu____11334 =
                let uu____11361 =
                  let uu____11388 =
                    let uu____11413 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11413)  in
                  [uu____11388;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11361  in
              uu____11266 :: uu____11334  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11239  in
          uu____11144 :: uu____11212  in
        uu____11049 :: uu____11117  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11958 = encode_formula phi' env  in
            (match uu____11958 with
             | (phi2,decls) ->
                 let uu____11969 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11969, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11971 ->
            let uu____11978 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11978 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12017 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12017 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12029;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12031;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12033;
                 FStar_Syntax_Syntax.lbpos = uu____12034;_}::[]),e2)
            ->
            let uu____12061 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12061 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12114::(x,uu____12116)::(t,uu____12118)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12185 = encode_term x env  in
                 (match uu____12185 with
                  | (x1,decls) ->
                      let uu____12196 = encode_term t env  in
                      (match uu____12196 with
                       | (t1,decls') ->
                           let uu____12207 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12207, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12210)::(msg,uu____12212)::(phi2,uu____12214)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12281 =
                   let uu____12286 =
                     let uu____12287 = FStar_Syntax_Subst.compress r  in
                     uu____12287.FStar_Syntax_Syntax.n  in
                   let uu____12290 =
                     let uu____12291 = FStar_Syntax_Subst.compress msg  in
                     uu____12291.FStar_Syntax_Syntax.n  in
                   (uu____12286, uu____12290)  in
                 (match uu____12281 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12300))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12311 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12318)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12353 when head_redex env head2 ->
                 let uu____12368 = whnf env phi1  in
                 encode_formula uu____12368 env
             | uu____12369 ->
                 let uu____12384 = encode_term phi1 env  in
                 (match uu____12384 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12396 =
                          let uu____12398 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12399 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12398 uu____12399
                           in
                        if uu____12396
                        then tt
                        else
                          (let uu___371_12403 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___371_12403.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___371_12403.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12404 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12404, decls)))
        | uu____12405 ->
            let uu____12406 = encode_term phi1 env  in
            (match uu____12406 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12418 =
                     let uu____12420 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12421 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12420 uu____12421  in
                   if uu____12418
                   then tt
                   else
                     (let uu___372_12425 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___372_12425.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___372_12425.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12426 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12426, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12470 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12470 with
        | (vars,guards,env2,decls,uu____12509) ->
            let uu____12522 = encode_smt_patterns ps env2  in
            (match uu____12522 with
             | (pats,decls') ->
                 let uu____12565 = encode_formula body env2  in
                 (match uu____12565 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12597;
                             FStar_SMTEncoding_Term.rng = uu____12598;_}::[])::[]
                            when
                            let uu____12615 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12615 = gf -> []
                        | uu____12618 -> guards  in
                      let uu____12623 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12623, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12634 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12634 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12643 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12749  ->
                     match uu____12749 with
                     | (l,uu____12774) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12643 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12843,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12935 = encode_q_body env vars pats body  in
             match uu____12935 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12980 =
                     let uu____12991 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12991)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12980
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13022 = encode_q_body env vars pats body  in
             match uu____13022 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13066 =
                   let uu____13067 =
                     let uu____13078 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13078)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13067
                    in
                 (uu____13066, decls))))
