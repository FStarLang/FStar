open Prims
let mkForall_fuel' :
  'Auu____5 .
    FStar_Range.range ->
      'Auu____5 ->
        (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
          FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
          FStar_SMTEncoding_Term.term
  =
  fun r  ->
    fun n1  ->
      fun uu____27  ->
        match uu____27 with
        | (pats,vars,body) ->
            let fallback uu____52 =
              FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
            let uu____57 = FStar_Options.unthrottle_inductives ()  in
            if uu____57
            then fallback ()
            else
              (let uu____59 =
                 FStar_SMTEncoding_Env.fresh_fvar "f"
                   FStar_SMTEncoding_Term.Fuel_sort
                  in
               match uu____59 with
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
                             | uu____90 -> p))
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
                               let uu____111 = add_fuel1 guards  in
                               FStar_SMTEncoding_Util.mk_and_l uu____111
                           | uu____114 ->
                               let uu____115 = add_fuel1 [guard]  in
                               FStar_All.pipe_right uu____115 FStar_List.hd
                            in
                         FStar_SMTEncoding_Util.mkImp (guard1, body')
                     | uu____120 -> body  in
                   let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                     vars  in
                   FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
      FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
      FStar_SMTEncoding_Term.term)
  = fun r  -> mkForall_fuel' r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____164 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____177 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____184 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____185 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____202 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____219 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____221 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____221 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____239;
             FStar_Syntax_Syntax.vars = uu____240;_},uu____241)
          ->
          let uu____262 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____262 FStar_Option.isNone
      | uu____279 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____286 =
        let uu____287 = FStar_Syntax_Util.un_uinst t  in
        uu____287.FStar_Syntax_Syntax.n  in
      match uu____286 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____290,uu____291,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___65_312  ->
                  match uu___65_312 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____313 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____315 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____315 FStar_Option.isSome
      | uu____332 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____339 = head_normal env t  in
      if uu____339
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses]
          env.FStar_SMTEncoding_Env.tcenv t
  
let (norm :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses]
        env.FStar_SMTEncoding_Env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____350 =
      let uu____351 = FStar_Syntax_Syntax.null_binder t  in [uu____351]  in
    let uu____352 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____350 uu____352 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____390 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____390
                | s ->
                    let uu____395 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____395) e)
  
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
          let uu____430 =
            let uu____435 =
              let uu____436 = FStar_Util.string_of_int arity  in
              let uu____437 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____436 uu____437
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____435)  in
          FStar_Errors.raise_error uu____430 rng
  
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
              (let uu____468 = FStar_Util.first_N arity args  in
               match uu____468 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____491 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____491 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___66_498  ->
    match uu___66_498 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____499 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____535;
                       FStar_SMTEncoding_Term.rng = uu____536;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____559) ->
              let uu____568 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____579 -> false) args (FStar_List.rev xs))
                 in
              if uu____568
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____583,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____587 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____591 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____591))
                 in
              if uu____587
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____595 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____607 'Auu____608 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv,'Auu____607) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____608) FStar_Pervasives_Native.tuple2
          Prims.list -> Prims.unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____663  ->
                  match uu____663 with
                  | (x,uu____669) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                        FStar_TypeChecker_Normalize.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____677 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____689 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____689) uu____677 tl1
               in
            let uu____692 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____719  ->
                      match uu____719 with
                      | (b,uu____725) ->
                          let uu____726 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____726))
               in
            (match uu____692 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____732) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____746 =
                   let uu____751 =
                     let uu____752 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____752
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____751)
                    in
                 FStar_Errors.log_issue pos uu____746)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____983 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____996 ->
            let uu____1003 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1003
        | uu____1004 ->
            if norm1
            then let uu____1005 = whnf env t1  in aux false uu____1005
            else
              (let uu____1007 =
                 let uu____1008 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1009 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1008 uu____1009
                  in
               failwith uu____1007)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1041) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1046 ->
        let uu____1047 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1047)
  
let is_arithmetic_primitive :
  'Auu____1061 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1061 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1081::uu____1082::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1086::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1089 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1110 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1125 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1129 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1129)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1168)::uu____1169::uu____1170::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1221)::uu____1222::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1259 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1492 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1492, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1495 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1495, [])
      | FStar_Const.Const_char c1 ->
          let uu____1499 =
            let uu____1500 =
              let uu____1507 =
                let uu____1510 =
                  let uu____1511 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1511  in
                [uu____1510]  in
              ("FStar.Char.__char_of_int", uu____1507)  in
            FStar_SMTEncoding_Util.mkApp uu____1500  in
          (uu____1499, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1527 =
            let uu____1528 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1528  in
          (uu____1527, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1549) ->
          let uu____1550 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1550, [])
      | FStar_Const.Const_range uu____1553 ->
          let uu____1554 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1554, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1560 =
            let uu____1561 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1561  in
          failwith uu____1560

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,FStar_SMTEncoding_Env.env_t,
          FStar_SMTEncoding_Term.decls_t,FStar_Syntax_Syntax.bv Prims.list)
          FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____1590 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1590
         then
           let uu____1591 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1591
         else ());
        (let uu____1593 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1677  ->
                   fun b  ->
                     match uu____1677 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1756 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____1772 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____1772 with
                           | (xxsym,xx,env') ->
                               let uu____1796 =
                                 let uu____1801 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____1801 env1 xx
                                  in
                               (match uu____1796 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1756 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1593 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____1960 = encode_term t env  in
          match uu____1960 with
          | (t1,decls) ->
              let uu____1971 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____1971, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____1982 = encode_term t env  in
          match uu____1982 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____1997 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____1997, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____1999 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____1999, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2005 = encode_args args_e env  in
        match uu____2005 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2024 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2033 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2033  in
            let binary arg_tms1 =
              let uu____2046 =
                let uu____2047 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2047  in
              let uu____2048 =
                let uu____2049 =
                  let uu____2050 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2050  in
                FStar_SMTEncoding_Term.unboxInt uu____2049  in
              (uu____2046, uu____2048)  in
            let mk_default uu____2056 =
              let uu____2057 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2057 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l a op mk_args ts =
              let uu____2107 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2107
              then
                let uu____2108 =
                  let uu____2109 = mk_args ts  in op uu____2109  in
                FStar_All.pipe_right uu____2108 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2138 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2138
              then
                let uu____2139 = binary ts  in
                match uu____2139 with
                | (t1,t2) ->
                    let uu____2146 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2146
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2150 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2150
                 then
                   let uu____2151 = op (binary ts)  in
                   FStar_All.pipe_right uu____2151
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 =
              mk_l ()
                (fun a403  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a403)
                (fun a404  -> (Obj.magic binary) a404)
               in
            let sub1 =
              mk_l ()
                (fun a405  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a405)
                (fun a406  -> (Obj.magic binary) a406)
               in
            let minus =
              mk_l ()
                (fun a407  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a407)
                (fun a408  -> (Obj.magic unary) a408)
               in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____2274 =
              let uu____2283 =
                FStar_List.tryFind
                  (fun uu____2305  ->
                     match uu____2305 with
                     | (l,uu____2315) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2283 FStar_Util.must  in
            (match uu____2274 with
             | (uu____2354,op) ->
                 let uu____2364 = op arg_tms  in (uu____2364, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2372 = FStar_List.hd args_e  in
        match uu____2372 with
        | (tm_sz,uu____2380) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2390 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2390 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2398 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2398);
                   t_decls1)
               in
            let uu____2399 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2419::(sz_arg,uu____2421)::uu____2422::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2471 =
                    let uu____2474 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2474  in
                  let uu____2477 =
                    let uu____2480 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2480  in
                  (uu____2471, uu____2477)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2486::(sz_arg,uu____2488)::uu____2489::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2538 =
                    let uu____2539 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2539
                     in
                  failwith uu____2538
              | uu____2548 ->
                  let uu____2555 = FStar_List.tail args_e  in
                  (uu____2555, FStar_Pervasives_Native.None)
               in
            (match uu____2399 with
             | (arg_tms,ext_sz) ->
                 let uu____2578 = encode_args arg_tms env  in
                 (match uu____2578 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2599 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2608 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2608  in
                      let unary_arith arg_tms2 =
                        let uu____2617 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2617  in
                      let binary arg_tms2 =
                        let uu____2630 =
                          let uu____2631 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2631
                           in
                        let uu____2632 =
                          let uu____2633 =
                            let uu____2634 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2634  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2633
                           in
                        (uu____2630, uu____2632)  in
                      let binary_arith arg_tms2 =
                        let uu____2649 =
                          let uu____2650 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2650
                           in
                        let uu____2651 =
                          let uu____2652 =
                            let uu____2653 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2653  in
                          FStar_SMTEncoding_Term.unboxInt uu____2652  in
                        (uu____2649, uu____2651)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____2695 =
                          let uu____2696 = mk_args ts  in op uu____2696  in
                        FStar_All.pipe_right uu____2695 resBox  in
                      let bv_and =
                        mk_bv ()
                          (fun a409  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a409)
                          (fun a410  -> (Obj.magic binary) a410)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a411  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a411)
                          (fun a412  -> (Obj.magic binary) a412)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a413  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a413)
                          (fun a414  -> (Obj.magic binary) a414)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a415  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a415)
                          (fun a416  -> (Obj.magic binary) a416)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a417  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a417)
                          (fun a418  -> (Obj.magic binary) a418)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a419  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a419)
                          (fun a420  -> (Obj.magic binary_arith) a420)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a421  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a421)
                          (fun a422  -> (Obj.magic binary_arith) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a423)
                          (fun a424  -> (Obj.magic binary_arith) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a425)
                          (fun a426  -> (Obj.magic binary_arith) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a427  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a427)
                          (fun a428  -> (Obj.magic binary_arith) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a429  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a429)
                          (fun a430  -> (Obj.magic binary) a430)
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____2760 =
                          let uu____2763 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____2763  in
                        let uu____2765 =
                          let uu____2768 =
                            let uu____2769 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____2769  in
                          FStar_SMTEncoding_Term.boxBitVec uu____2768  in
                        mk_bv () (fun a431  -> (Obj.magic uu____2760) a431)
                          (fun a432  -> (Obj.magic unary) a432) uu____2765
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a433  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a433) (fun a434  -> (Obj.magic unary) a434)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a435  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a435)
                          (fun a436  -> (Obj.magic unary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
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
                      let uu____2968 =
                        let uu____2977 =
                          FStar_List.tryFind
                            (fun uu____2999  ->
                               match uu____2999 with
                               | (l,uu____3009) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____2977 FStar_Util.must  in
                      (match uu____2968 with
                       | (uu____3050,op) ->
                           let uu____3060 = op arg_tms1  in
                           (uu____3060, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___70_3070 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___70_3070.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___70_3070.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___70_3070.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___70_3070.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___70_3070.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___70_3070.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___70_3070.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___70_3070.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___70_3070.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___70_3070.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3071 = encode_term t env1  in
      match uu____3071 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3092 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3092 with
           | FStar_Pervasives_Native.Some uu____3099 -> (tm, decls)
           | uu____3100 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3107,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3108;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3109;
                                  FStar_SMTEncoding_Term.rng = uu____3110;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3111;
                       FStar_SMTEncoding_Term.freevars = uu____3112;
                       FStar_SMTEncoding_Term.rng = uu____3113;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3141 ->
                    let uu____3142 = encode_formula t env1  in
                    (match uu____3142 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3158 =
                                 let uu____3163 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3163, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3158
                           | uu____3164 ->
                               let uu____3165 =
                                 let uu____3176 =
                                   let uu____3177 =
                                     let uu____3182 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3182, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3177
                                    in
                                 ([[valid_tm]], vars, uu____3176)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3165
                            in
                         let ax =
                           let uu____3192 =
                             let uu____3199 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3199)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3192  in
                         ((let uu____3203 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3203);
                          (tm,
                            (FStar_List.append decls
                               (FStar_List.append decls' [ax])))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3214 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3214
       then
         let uu____3215 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3216 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3217 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3215 uu____3216
           uu____3217
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3223 ->
           let uu____3248 =
             let uu____3249 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3250 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3251 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3252 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3249
               uu____3250 uu____3251 uu____3252
              in
           failwith uu____3248
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3257 =
             let uu____3258 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3259 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3260 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3261 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3258
               uu____3259 uu____3260 uu____3261
              in
           failwith uu____3257
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3267 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____3267 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3269 =
             let uu____3270 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3270
              in
           failwith uu____3269
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3277),uu____3278) ->
           let uu____3327 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3335 -> false  in
           if uu____3327
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3352) ->
           let tv =
             let uu____3358 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3358
              in
           let t1 =
             let uu____3362 =
               let uu____3371 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____3371]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3362
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____3373) ->
           encode_term t1
             (let uu___71_3389 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___71_3389.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___71_3389.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___71_3389.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___71_3389.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___71_3389.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___71_3389.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___71_3389.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___71_3389.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___71_3389.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___71_3389.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3391) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3401 = head_redex env t  in
           if uu____3401
           then let uu____3406 = whnf env t  in encode_term uu____3406 env
           else
             (let uu____3408 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3408 with
              | (uu____3417,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3427 ->
                          let uu____3432 =
                            let uu____3433 =
                              let uu____3440 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3441 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3440,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3441)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3433  in
                          [uu____3432]
                      | FStar_SMTEncoding_Term.App (uu____3444,[]) ->
                          let uu____3447 =
                            let uu____3448 =
                              let uu____3455 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3456 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3455,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3456)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3448  in
                          [uu____3447]
                      | uu____3459 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____3463 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3467) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____3492 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____3492 with
            | (binders1,res) ->
                let uu____3503 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____3503
                then
                  let uu____3508 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____3508 with
                   | (vars,guards,env',decls,uu____3533) ->
                       let fsym =
                         let uu____3551 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____3551, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3554 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___72_3563 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___72_3563.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___72_3563.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___72_3563.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___72_3563.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___72_3563.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___72_3563.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___72_3563.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___72_3563.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___72_3563.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___72_3563.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___72_3563.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___72_3563.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___72_3563.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___72_3563.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___72_3563.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___72_3563.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___72_3563.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___72_3563.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___72_3563.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___72_3563.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___72_3563.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___72_3563.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___72_3563.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___72_3563.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___72_3563.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___72_3563.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___72_3563.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___72_3563.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___72_3563.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___72_3563.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___72_3563.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___72_3563.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___72_3563.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___72_3563.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___72_3563.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___72_3563.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____3554 with
                        | (pre_opt,res_t) ->
                            let uu____3574 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____3574 with
                             | (res_pred,decls') ->
                                 let uu____3585 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3598 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____3598, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3602 =
                                         encode_formula pre env'  in
                                       (match uu____3602 with
                                        | (guard,decls0) ->
                                            let uu____3615 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____3615, decls0))
                                    in
                                 (match uu____3585 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3627 =
                                          let uu____3638 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____3638)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____3627
                                         in
                                      let cvars =
                                        let uu____3656 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____3656
                                          (FStar_List.filter
                                             (fun uu____3670  ->
                                                match uu____3670 with
                                                | (x,uu____3676) ->
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
                                      let uu____3695 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____3695 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3703 =
                                             let uu____3704 =
                                               let uu____3711 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____3711)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3704
                                              in
                                           (uu____3703,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3731 =
                                               let uu____3732 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3732
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____3731
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____3743 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____3743
                                             then
                                               let uu____3746 =
                                                 let uu____3747 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____3747 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____3746
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
                                             let uu____3757 =
                                               let uu____3764 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____3764)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3757
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
                                             let uu____3776 =
                                               let uu____3783 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____3783,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3776
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
                                             let uu____3804 =
                                               let uu____3811 =
                                                 let uu____3812 =
                                                   let uu____3823 =
                                                     let uu____3824 =
                                                       let uu____3829 =
                                                         let uu____3830 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3830
                                                          in
                                                       (f_has_t, uu____3829)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3824
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3823)
                                                    in
                                                 let uu____3849 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____3849 uu____3812  in
                                               (uu____3811,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3804
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____3866 =
                                               let uu____3873 =
                                                 let uu____3874 =
                                                   let uu____3885 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3885)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____3874
                                                  in
                                               (uu____3873,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3866
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
                                           ((let uu____3910 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____3910);
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
                     let uu____3925 =
                       let uu____3932 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____3932,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3925  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____3944 =
                       let uu____3951 =
                         let uu____3952 =
                           let uu____3963 =
                             let uu____3964 =
                               let uu____3969 =
                                 let uu____3970 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3970
                                  in
                               (f_has_t, uu____3969)  in
                             FStar_SMTEncoding_Util.mkImp uu____3964  in
                           ([[f_has_t]], [fsym], uu____3963)  in
                         let uu____3993 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____3993 uu____3952  in
                       (uu____3951, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3944  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4010 ->
           let uu____4017 =
             let uu____4022 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4022 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4029;
                 FStar_Syntax_Syntax.vars = uu____4030;_} ->
                 let uu____4037 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4037 with
                  | (b,f1) ->
                      let uu____4062 =
                        let uu____4063 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4063  in
                      (uu____4062, f1))
             | uu____4072 -> failwith "impossible"  in
           (match uu____4017 with
            | (x,f) ->
                let uu____4083 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4083 with
                 | (base_t,decls) ->
                     let uu____4094 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4094 with
                      | (x1,xtm,env') ->
                          let uu____4108 = encode_formula f env'  in
                          (match uu____4108 with
                           | (refinement,decls') ->
                               let uu____4119 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4119 with
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
                                      let uu____4135 =
                                        let uu____4138 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4145 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4138
                                          uu____4145
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4135
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4178  ->
                                              match uu____4178 with
                                              | (y,uu____4184) ->
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
                                    let uu____4217 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4217 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4225 =
                                           let uu____4226 =
                                             let uu____4233 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4233)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4226
                                            in
                                         (uu____4225,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4254 =
                                             let uu____4255 =
                                               let uu____4256 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4256
                                                in
                                             Prims.strcat module_name
                                               uu____4255
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4254
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
                                           let uu____4270 =
                                             let uu____4277 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4277)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4270
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
                                           let uu____4292 =
                                             let uu____4299 =
                                               let uu____4300 =
                                                 let uu____4311 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4311)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4300
                                                in
                                             (uu____4299,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4292
                                            in
                                         let t_kinding =
                                           let uu____4329 =
                                             let uu____4336 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4336,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4329
                                            in
                                         let t_interp =
                                           let uu____4354 =
                                             let uu____4361 =
                                               let uu____4362 =
                                                 let uu____4373 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4373)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4362
                                                in
                                             (uu____4361,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4354
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4402 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4402);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4432 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4432  in
           let uu____4433 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____4433 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4445 =
                    let uu____4452 =
                      let uu____4453 =
                        let uu____4454 =
                          let uu____4455 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4455
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____4454  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4453
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4452)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4445  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4460 ->
           let uu____4475 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4475 with
            | (head1,args_e) ->
                let uu____4516 =
                  let uu____4529 =
                    let uu____4530 = FStar_Syntax_Subst.compress head1  in
                    uu____4530.FStar_Syntax_Syntax.n  in
                  (uu____4529, args_e)  in
                (match uu____4516 with
                 | uu____4545 when head_redex env head1 ->
                     let uu____4558 = whnf env t  in
                     encode_term uu____4558 env
                 | uu____4559 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____4578 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4592) when
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
                       FStar_Syntax_Syntax.pos = uu____4610;
                       FStar_Syntax_Syntax.vars = uu____4611;_},uu____4612),uu____4613)
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
                       FStar_Syntax_Syntax.pos = uu____4635;
                       FStar_Syntax_Syntax.vars = uu____4636;_},uu____4637),uu____4638::
                    (v1,uu____4640)::(v2,uu____4642)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4693 = encode_term v1 env  in
                     (match uu____4693 with
                      | (v11,decls1) ->
                          let uu____4704 = encode_term v2 env  in
                          (match uu____4704 with
                           | (v21,decls2) ->
                               let uu____4715 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4715,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4719::(v1,uu____4721)::(v2,uu____4723)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4770 = encode_term v1 env  in
                     (match uu____4770 with
                      | (v11,decls1) ->
                          let uu____4781 = encode_term v2 env  in
                          (match uu____4781 with
                           | (v21,decls2) ->
                               let uu____4792 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4792,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____4796)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____4822)::(rng,uu____4824)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4859) ->
                     let e0 =
                       let uu____4877 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____4877
                        in
                     ((let uu____4885 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____4885
                       then
                         let uu____4886 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4886
                       else ());
                      (let e =
                         let uu____4891 =
                           let uu____4892 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____4893 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4892
                             uu____4893
                            in
                         uu____4891 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4902),(arg,uu____4904)::[]) -> encode_term arg env
                 | uu____4929 ->
                     let uu____4942 = encode_args args_e env  in
                     (match uu____4942 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4997 = encode_term head1 env  in
                            match uu____4997 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5061 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5061 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5139  ->
                                                 fun uu____5140  ->
                                                   match (uu____5139,
                                                           uu____5140)
                                                   with
                                                   | ((bv,uu____5162),
                                                      (a,uu____5164)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5182 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5182
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5187 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5187 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5202 =
                                                   let uu____5209 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5218 =
                                                     let uu____5219 =
                                                       let uu____5220 =
                                                         let uu____5221 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5221
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5220
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5219
                                                      in
                                                   (uu____5209,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5218)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5202
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5238 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5238 with
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
                                   FStar_Syntax_Syntax.pos = uu____5270;
                                   FStar_Syntax_Syntax.vars = uu____5271;_},uu____5272)
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
                                   FStar_Syntax_Syntax.pos = uu____5283;
                                   FStar_Syntax_Syntax.vars = uu____5284;_},uu____5285)
                                ->
                                let uu____5290 =
                                  let uu____5291 =
                                    let uu____5296 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5296
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5291
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5290
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5326 =
                                  let uu____5327 =
                                    let uu____5332 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5332
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5327
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5326
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5361,(FStar_Util.Inl t1,uu____5363),uu____5364)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5413,(FStar_Util.Inr c,uu____5415),uu____5416)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5465 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5492 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5492
                                  in
                               let uu____5493 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____5493 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5509;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5510;_},uu____5511)
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
                                     | uu____5525 ->
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
           let uu____5574 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____5574 with
            | (bs1,body1,opening) ->
                let fallback uu____5597 =
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
                  let uu____5604 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____5604, [decl])  in
                let is_impure rc =
                  let uu____5611 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____5611 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5621 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____5621
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____5639 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____5639
                  then
                    let uu____5642 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____5642
                  else
                    (let uu____5644 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____5644
                     then
                       let uu____5647 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____5647
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5654 =
                         let uu____5659 =
                           let uu____5660 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____5660
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____5659)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____5654);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5662 =
                       (is_impure rc) &&
                         (let uu____5664 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____5664)
                        in
                     if uu____5662
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____5671 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____5671 with
                        | (vars,guards,envbody,decls,uu____5696) ->
                            let body2 =
                              let uu____5710 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____5710
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____5712 = encode_term body2 envbody  in
                            (match uu____5712 with
                             | (body3,decls') ->
                                 let uu____5723 =
                                   let uu____5732 = codomain_eff rc  in
                                   match uu____5732 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____5751 = encode_term tfun env
                                          in
                                       (match uu____5751 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____5723 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5783 =
                                          let uu____5794 =
                                            let uu____5795 =
                                              let uu____5800 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____5800, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5795
                                             in
                                          ([], vars, uu____5794)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____5783
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
                                            let uu____5812 =
                                              let uu____5815 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____5815
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5812
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
                                      let uu____5834 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____5834 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5842 =
                                             let uu____5843 =
                                               let uu____5850 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____5850)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5843
                                              in
                                           (uu____5842,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5861 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____5861 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5872 =
                                                    let uu____5873 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____5873 = cache_size
                                                     in
                                                  if uu____5872
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
                                                    let uu____5889 =
                                                      let uu____5890 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5890
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____5889
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
                                                  let uu____5897 =
                                                    let uu____5904 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____5904)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5897
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
                                                      let uu____5922 =
                                                        let uu____5923 =
                                                          let uu____5930 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____5930,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5923
                                                         in
                                                      [uu____5922]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____5943 =
                                                    let uu____5950 =
                                                      let uu____5951 =
                                                        let uu____5962 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5962)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____5951
                                                       in
                                                    (uu____5950,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5943
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
                                                ((let uu____5979 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____5979);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5982,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5983;
                          FStar_Syntax_Syntax.lbunivs = uu____5984;
                          FStar_Syntax_Syntax.lbtyp = uu____5985;
                          FStar_Syntax_Syntax.lbeff = uu____5986;
                          FStar_Syntax_Syntax.lbdef = uu____5987;
                          FStar_Syntax_Syntax.lbattrs = uu____5988;
                          FStar_Syntax_Syntax.lbpos = uu____5989;_}::uu____5990),uu____5991)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6021;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6023;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6025;
                FStar_Syntax_Syntax.lbpos = uu____6026;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6050 ->
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
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____6120 =
                let uu____6125 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6125 env  in
              match uu____6120 with
              | (ee1,decls1) ->
                  let uu____6146 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6146 with
                   | (xs,e21) ->
                       let uu____6171 = FStar_List.hd xs  in
                       (match uu____6171 with
                        | (x1,uu____6185) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6187 = encode_body e21 env'  in
                            (match uu____6187 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____6219 =
              let uu____6226 =
                let uu____6227 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6227  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6226  in
            match uu____6219 with
            | (scrsym,scr',env1) ->
                let uu____6235 = encode_term e env1  in
                (match uu____6235 with
                 | (scr,decls) ->
                     let uu____6246 =
                       let encode_branch b uu____6271 =
                         match uu____6271 with
                         | (else_case,decls1) ->
                             let uu____6290 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____6290 with
                              | (p,w,br) ->
                                  let uu____6316 = encode_pat env1 p  in
                                  (match uu____6316 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6353  ->
                                                   match uu____6353 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____6360 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6382 =
                                               encode_term w1 env2  in
                                             (match uu____6382 with
                                              | (w2,decls2) ->
                                                  let uu____6395 =
                                                    let uu____6396 =
                                                      let uu____6401 =
                                                        let uu____6402 =
                                                          let uu____6407 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____6407)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6402
                                                         in
                                                      (guard, uu____6401)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6396
                                                     in
                                                  (uu____6395, decls2))
                                          in
                                       (match uu____6360 with
                                        | (guard1,decls2) ->
                                            let uu____6420 =
                                              encode_br br env2  in
                                            (match uu____6420 with
                                             | (br1,decls3) ->
                                                 let uu____6433 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____6433,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6246 with
                      | (match_tm,decls1) ->
                          let uu____6452 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____6452, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____6492 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____6492
       then
         let uu____6493 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6493
       else ());
      (let uu____6495 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____6495 with
       | (vars,pat_term) ->
           let uu____6512 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6565  ->
                     fun v1  ->
                       match uu____6565 with
                       | (env1,vars1) ->
                           let uu____6617 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____6617 with
                            | (xx,uu____6639,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____6512 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____6718 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____6719 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____6720 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____6728 = encode_const c env1  in
                      (match uu____6728 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____6742::uu____6743 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____6746 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____6769 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____6769 with
                        | (uu____6776,uu____6777::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____6780 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6813  ->
                                  match uu____6813 with
                                  | (arg,uu____6821) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____6827 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____6827))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6854) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6885 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6908 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6952  ->
                                  match uu____6952 with
                                  | (arg,uu____6966) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____6972 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____6972))
                         in
                      FStar_All.pipe_right uu____6908 FStar_List.flatten
                   in
                let pat_term1 uu____7000 = encode_term pat_term env1  in
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
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____7010 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7048  ->
                fun uu____7049  ->
                  match (uu____7048, uu____7049) with
                  | ((tms,decls),(t,uu____7085)) ->
                      let uu____7106 = encode_term t env  in
                      (match uu____7106 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7010 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7163 = FStar_Syntax_Util.list_elements e  in
        match uu____7163 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7188 =
          let uu____7203 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7203 FStar_Syntax_Util.head_and_args  in
        match uu____7188 with
        | (head1,args) ->
            let uu____7246 =
              let uu____7259 =
                let uu____7260 = FStar_Syntax_Util.un_uinst head1  in
                uu____7260.FStar_Syntax_Syntax.n  in
              (uu____7259, args)  in
            (match uu____7246 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7278,uu____7279)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____7317 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____7361 =
            let uu____7376 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____7376 FStar_Syntax_Util.head_and_args
             in
          match uu____7361 with
          | (head1,args) ->
              let uu____7417 =
                let uu____7430 =
                  let uu____7431 = FStar_Syntax_Util.un_uinst head1  in
                  uu____7431.FStar_Syntax_Syntax.n  in
                (uu____7430, args)  in
              (match uu____7417 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____7448)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____7475 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____7501 = smt_pat_or1 t1  in
            (match uu____7501 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____7521 = list_elements1 e  in
                 FStar_All.pipe_right uu____7521
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____7547 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____7547
                           (FStar_List.map one_pat)))
             | uu____7566 ->
                 let uu____7571 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____7571])
        | uu____7612 ->
            let uu____7615 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____7615]
         in
      let uu____7656 =
        let uu____7679 =
          let uu____7680 = FStar_Syntax_Subst.compress t  in
          uu____7680.FStar_Syntax_Syntax.n  in
        match uu____7679 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____7723 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____7723 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____7774;
                        FStar_Syntax_Syntax.effect_name = uu____7775;
                        FStar_Syntax_Syntax.result_typ = uu____7776;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____7778)::(post,uu____7780)::(pats,uu____7782)::[];
                        FStar_Syntax_Syntax.flags = uu____7783;_}
                      ->
                      let uu____7824 = lemma_pats pats  in
                      (binders1, pre, post, uu____7824)
                  | uu____7849 -> failwith "impos"))
        | uu____7872 -> failwith "Impos"  in
      match uu____7656 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___73_7932 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___73_7932.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___73_7932.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___73_7932.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___73_7932.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___73_7932.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___73_7932.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___73_7932.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___73_7932.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___73_7932.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___73_7932.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____7933 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____7933 with
           | (vars,guards,env2,decls,uu____7958) ->
               let uu____7971 = encode_smt_patterns patterns env2  in
               (match uu____7971 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___74_8004 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___74_8004.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___74_8004.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___74_8004.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___74_8004.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___74_8004.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___74_8004.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___74_8004.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___74_8004.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___74_8004.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___74_8004.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____8005 =
                      let uu____8010 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8010 env3  in
                    (match uu____8005 with
                     | (pre1,decls'') ->
                         let uu____8017 =
                           let uu____8022 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8022 env3  in
                         (match uu____8017 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8032 =
                                let uu____8033 =
                                  let uu____8044 =
                                    let uu____8045 =
                                      let uu____8050 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8050, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8045
                                     in
                                  (pats, vars, uu____8044)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____8033
                                 in
                              (uu____8032, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list,FStar_SMTEncoding_Term.decl
                                                           Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___75_8076 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___75_8076.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___75_8076.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___75_8076.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___75_8076.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___75_8076.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___75_8076.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___75_8076.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___75_8076.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___75_8076.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___75_8076.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____8087 = FStar_Syntax_Util.head_and_args t  in
        match uu____8087 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8146::(x,uu____8148)::(t1,uu____8150)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8197 = encode_term x env1  in
                 (match uu____8197 with
                  | (x1,decls) ->
                      let uu____8210 = encode_term t1 env1  in
                      (match uu____8210 with
                       | (t2,decls') ->
                           let uu____8223 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____8223, (FStar_List.append decls decls'))))
             | uu____8226 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____8263  ->
             match uu____8263 with
             | (pats_l1,decls) ->
                 let uu____8304 =
                   FStar_List.fold_right
                     (fun uu____8335  ->
                        fun uu____8336  ->
                          match (uu____8335, uu____8336) with
                          | ((p,uu____8370),(pats1,decls1)) ->
                              let uu____8393 = encode_smt_pattern p  in
                              (match uu____8393 with
                               | (t,d) ->
                                   let uu____8414 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____8414 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____8431 =
                                            let uu____8436 =
                                              let uu____8437 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____8438 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____8437 uu____8438
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____8436)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____8431);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____8304 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____8493 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____8493
        then
          let uu____8494 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____8495 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____8494 uu____8495
        else ()  in
      let enc f r l =
        let uu____8528 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____8556 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____8556 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____8528 with
        | (decls,args) ->
            let uu____8585 =
              let uu___76_8586 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___76_8586.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___76_8586.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____8585, decls)
         in
      let const_op f r uu____8617 = let uu____8630 = f r  in (uu____8630, [])
         in
      let un_op f l =
        let uu____8649 = FStar_List.hd l  in FStar_All.pipe_left f uu____8649
         in
      let bin_op f uu___67_8665 =
        match uu___67_8665 with
        | t1::t2::[] -> f (t1, t2)
        | uu____8676 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____8710 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____8733  ->
                 match uu____8733 with
                 | (t,uu____8747) ->
                     let uu____8748 = encode_formula t env  in
                     (match uu____8748 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____8710 with
        | (decls,phis) ->
            let uu____8777 =
              let uu___77_8778 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___77_8778.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___77_8778.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____8777, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____8839  ->
               match uu____8839 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____8858) -> false
                    | uu____8859 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____8874 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____8874
        else
          (let uu____8888 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____8888 r rf)
         in
      let mk_imp1 r uu___68_8913 =
        match uu___68_8913 with
        | (lhs,uu____8919)::(rhs,uu____8921)::[] ->
            let uu____8948 = encode_formula rhs env  in
            (match uu____8948 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____8963) ->
                      (l1, decls1)
                  | uu____8968 ->
                      let uu____8969 = encode_formula lhs env  in
                      (match uu____8969 with
                       | (l2,decls2) ->
                           let uu____8980 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____8980, (FStar_List.append decls1 decls2)))))
        | uu____8983 -> failwith "impossible"  in
      let mk_ite r uu___69_9004 =
        match uu___69_9004 with
        | (guard,uu____9010)::(_then,uu____9012)::(_else,uu____9014)::[] ->
            let uu____9051 = encode_formula guard env  in
            (match uu____9051 with
             | (g,decls1) ->
                 let uu____9062 = encode_formula _then env  in
                 (match uu____9062 with
                  | (t,decls2) ->
                      let uu____9073 = encode_formula _else env  in
                      (match uu____9073 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9087 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____9112 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____9112  in
      let connectives =
        let uu____9130 =
          let uu____9143 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____9143)  in
        let uu____9160 =
          let uu____9175 =
            let uu____9188 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____9188)  in
          let uu____9205 =
            let uu____9220 =
              let uu____9235 =
                let uu____9248 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____9248)  in
              let uu____9265 =
                let uu____9280 =
                  let uu____9295 =
                    let uu____9308 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____9308)  in
                  [uu____9295;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____9280  in
              uu____9235 :: uu____9265  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____9220  in
          uu____9175 :: uu____9205  in
        uu____9130 :: uu____9160  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____9629 = encode_formula phi' env  in
            (match uu____9629 with
             | (phi2,decls) ->
                 let uu____9640 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____9640, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____9641 ->
            let uu____9648 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____9648 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____9687 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____9687 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____9699;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____9701;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____9703;
                 FStar_Syntax_Syntax.lbpos = uu____9704;_}::[]),e2)
            ->
            let uu____9728 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____9728 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9775::(x,uu____9777)::(t,uu____9779)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9826 = encode_term x env  in
                 (match uu____9826 with
                  | (x1,decls) ->
                      let uu____9837 = encode_term t env  in
                      (match uu____9837 with
                       | (t1,decls') ->
                           let uu____9848 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____9848, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____9853)::(msg,uu____9855)::(phi2,uu____9857)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____9902 =
                   let uu____9907 =
                     let uu____9908 = FStar_Syntax_Subst.compress r  in
                     uu____9908.FStar_Syntax_Syntax.n  in
                   let uu____9911 =
                     let uu____9912 = FStar_Syntax_Subst.compress msg  in
                     uu____9912.FStar_Syntax_Syntax.n  in
                   (uu____9907, uu____9911)  in
                 (match uu____9902 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____9921))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____9927 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____9934)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____9959 when head_redex env head2 ->
                 let uu____9972 = whnf env phi1  in
                 encode_formula uu____9972 env
             | uu____9973 ->
                 let uu____9986 = encode_term phi1 env  in
                 (match uu____9986 with
                  | (tt,decls) ->
                      let uu____9997 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___78_10000 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___78_10000.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___78_10000.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____9997, decls)))
        | uu____10001 ->
            let uu____10002 = encode_term phi1 env  in
            (match uu____10002 with
             | (tt,decls) ->
                 let uu____10013 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___79_10016 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___79_10016.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___79_10016.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____10013, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____10052 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____10052 with
        | (vars,guards,env2,decls,uu____10091) ->
            let uu____10104 = encode_smt_patterns ps env2  in
            (match uu____10104 with
             | (pats,decls') ->
                 let uu____10147 = encode_formula body env2  in
                 (match uu____10147 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____10179;
                             FStar_SMTEncoding_Term.rng = uu____10180;_}::[])::[]
                            when
                            let uu____10195 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____10195 = gf -> []
                        | uu____10196 -> guards  in
                      let uu____10201 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____10201, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____10212 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____10212 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____10221 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____10279  ->
                     match uu____10279 with
                     | (l,uu____10293) -> FStar_Ident.lid_equals op l))
              in
           (match uu____10221 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____10326,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____10366 = encode_q_body env vars pats body  in
             match uu____10366 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____10411 =
                     let uu____10422 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____10422)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____10411
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____10441 = encode_q_body env vars pats body  in
             match uu____10441 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____10485 =
                   let uu____10486 =
                     let uu____10497 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____10497)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____10486
                    in
                 (uu____10485, decls))))
