open Prims
let mkForall_fuel' :
  'Auu____14 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____14 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____45  ->
          match uu____45 with
          | (pats,vars,body) ->
              let fallback uu____73 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____78 = FStar_Options.unthrottle_inductives ()  in
              if uu____78
              then fallback ()
              else
                (let uu____83 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____83 with
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
                               | uu____123 -> p))
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
                                 let uu____144 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____144
                             | uu____147 ->
                                 let uu____148 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____148 FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____153 -> body  in
                     let vars1 =
                       let uu____165 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____165 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____229 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____245 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____253 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____255 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____269 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____289 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____292 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____292 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____311;
             FStar_Syntax_Syntax.vars = uu____312;_},uu____313)
          ->
          let uu____338 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____338 FStar_Option.isNone
      | uu____356 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____370 =
        let uu____371 = FStar_Syntax_Util.un_uinst t  in
        uu____371.FStar_Syntax_Syntax.n  in
      match uu____370 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____375,uu____376,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_401  ->
                  match uu___0_401 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____404 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____407 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____407 FStar_Option.isSome
      | uu____425 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____438 = head_normal env t  in
      if uu____438
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
    let uu____460 =
      let uu____461 = FStar_Syntax_Syntax.null_binder t  in [uu____461]  in
    let uu____480 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____460 uu____480 FStar_Pervasives_Native.None
  
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
                let uu____502 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____502 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____503 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____503
                | s ->
                    let uu____506 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____506) e)
  
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
          let uu____562 =
            let uu____568 =
              let uu____570 = FStar_Util.string_of_int arity  in
              let uu____572 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____570 uu____572
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____568)  in
          FStar_Errors.raise_error uu____562 rng
  
let (isTotFun_axioms :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.fvs -> Prims.bool -> FStar_SMTEncoding_Term.term)
  =
  fun pos  ->
    fun head1  ->
      fun vars  ->
        fun is_pure  ->
          let maybe_mkForall pat vars1 body =
            match vars1 with
            | [] -> body
            | uu____651 ->
                FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body)
             in
          let rec is_tot_fun_axioms ctx head2 vars1 =
            match vars1 with
            | [] -> FStar_SMTEncoding_Util.mkTrue
            | uu____730::[] ->
                if is_pure
                then
                  let uu____756 = FStar_SMTEncoding_Term.mk_IsTotFun head2
                     in
                  maybe_mkForall [[head2]] ctx uu____756
                else FStar_SMTEncoding_Util.mkTrue
            | x::vars2 ->
                let is_tot_fun_head =
                  let uu____792 = FStar_SMTEncoding_Term.mk_IsTotFun head2
                     in
                  maybe_mkForall [[head2]] ctx uu____792  in
                let app = mk_Apply head2 [x]  in
                let ctx1 = FStar_List.append ctx [x]  in
                let rest = is_tot_fun_axioms ctx1 app vars2  in
                FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
             in
          is_tot_fun_axioms [] head1 vars
  
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
                  (let uu____903 = FStar_Util.first_N arity args  in
                   match uu____903 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____927 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____927 arity n_args rng)
  
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
          let uu____950 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____950 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_959  ->
    match uu___1_959 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____965 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1013;
                       FStar_SMTEncoding_Term.rng = uu____1014;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1045) ->
              let uu____1055 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1072 -> false) args (FStar_List.rev xs))
                 in
              if uu____1055
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f  in
                ((let uu____1081 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp")
                     in
                  if uu____1081
                  then
                    let uu____1086 = FStar_SMTEncoding_Term.print_smt_term t
                       in
                    let uu____1088 =
                      match n1 with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x
                       in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1086 uu____1088
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1098,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1102 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1110 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1110))
                 in
              if uu____1102
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1117 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____1135 'Auu____1136 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1135) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1136) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1194  ->
                  match uu____1194 with
                  | (x,uu____1200) ->
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
              let uu____1208 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1220 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1220) uu____1208 tl1
               in
            let uu____1223 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1250  ->
                      match uu____1250 with
                      | (b,uu____1257) ->
                          let uu____1258 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1258))
               in
            (match uu____1223 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1265) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____1279 =
                   let uu____1285 =
                     let uu____1287 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1287
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1285)  in
                 FStar_Errors.log_issue pos uu____1279)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1573 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1588 ->
            let uu____1595 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1595
        | uu____1597 ->
            if norm1
            then let uu____1599 = whnf env t1  in aux false uu____1599
            else
              (let uu____1603 =
                 let uu____1605 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1607 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1605 uu____1607
                  in
               failwith uu____1603)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1649) ->
        let uu____1654 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1654 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1675 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1675)
              | uu____1682 -> (args, res)))
    | uu____1683 ->
        let uu____1684 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1684)
  
let is_arithmetic_primitive :
  'Auu____1698 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1698 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1721::uu____1722::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1726::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1729 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1760 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1783 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1793 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1793)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1835)::uu____1836::uu____1837::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1888)::uu____1889::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1926 -> false
  
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
          let uu____2250 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2250, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2252 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2252, [])
      | FStar_Const.Const_char c1 ->
          let uu____2255 =
            let uu____2256 =
              let uu____2264 =
                let uu____2267 =
                  let uu____2268 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2268  in
                [uu____2267]  in
              ("FStar.Char.__char_of_int", uu____2264)  in
            FStar_SMTEncoding_Util.mkApp uu____2256  in
          (uu____2255, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2286 =
            let uu____2287 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2287  in
          (uu____2286, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2308) ->
          let uu____2311 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2311, [])
      | FStar_Const.Const_range uu____2312 ->
          let uu____2313 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2313, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2316 =
            let uu____2317 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2317  in
          (uu____2316, [])
      | c1 ->
          let uu____2319 =
            let uu____2321 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2321  in
          failwith uu____2319

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
        (let uu____2350 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2350
         then
           let uu____2353 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2353
         else ());
        (let uu____2359 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2441  ->
                   fun b  ->
                     match uu____2441 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2506 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2522 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2522 with
                           | (xxsym,xx,env') ->
                               let uu____2547 =
                                 let uu____2552 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2552 env1 xx
                                  in
                               (match uu____2547 with
                                | (guard_x_t,decls') ->
                                    let uu____2567 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2567, guard_x_t, env', decls', x))
                            in
                         (match uu____2506 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2359 with
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
          let uu____2667 = encode_term t env  in
          match uu____2667 with
          | (t1,decls) ->
              let uu____2678 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2678, decls)

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
          let uu____2689 = encode_term t env  in
          match uu____2689 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2704 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2704, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2706 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2706, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2712 = encode_args args_e env  in
        match uu____2712 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2731 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2753 = FStar_List.hd arg_tms1  in unbox uu____2753
               in
            let binary unbox arg_tms1 =
              let uu____2778 =
                let uu____2779 = FStar_List.hd arg_tms1  in unbox uu____2779
                 in
              let uu____2780 =
                let uu____2781 =
                  let uu____2782 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2782  in
                unbox uu____2781  in
              (uu____2778, uu____2780)  in
            let mk_default uu____2790 =
              let uu____2791 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2791 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2880 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2880
              then
                let uu____2883 =
                  let uu____2884 = mk_args ts  in op uu____2884  in
                FStar_All.pipe_right uu____2883 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____2942 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2942
              then
                let uu____2945 = binary unbox ts  in
                match uu____2945 with
                | (t1,t2) ->
                    let uu____2952 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2952 box
              else
                (let uu____2958 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2958
                 then
                   let uu____2961 =
                     let uu____2962 = binary unbox ts  in op uu____2962  in
                   FStar_All.pipe_right uu____2961 box
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
            let uu____3397 =
              let uu____3407 =
                FStar_List.tryFind
                  (fun uu____3431  ->
                     match uu____3431 with
                     | (l,uu____3442) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3407 FStar_Util.must  in
            (match uu____3397 with
             | (uu____3486,op) ->
                 let uu____3498 = op arg_tms  in (uu____3498, decls))

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
        let uu____3514 = FStar_List.hd args_e  in
        match uu____3514 with
        | (tm_sz,uu____3530) ->
            let uu____3539 = uu____3514  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3550 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3576::(sz_arg,uu____3578)::uu____3579::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3646 =
                    let uu____3647 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3647  in
                  let uu____3674 =
                    let uu____3678 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3678  in
                  (uu____3646, uu____3674)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3685::(sz_arg,uu____3687)::uu____3688::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3755 =
                    let uu____3757 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3757
                     in
                  failwith uu____3755
              | uu____3767 ->
                  let uu____3782 = FStar_List.tail args_e  in
                  (uu____3782, FStar_Pervasives_Native.None)
               in
            (match uu____3550 with
             | (arg_tms,ext_sz) ->
                 let uu____3809 = encode_args arg_tms env  in
                 (match uu____3809 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3830 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3842 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3842  in
                      let unary_arith arg_tms2 =
                        let uu____3853 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3853  in
                      let binary arg_tms2 =
                        let uu____3868 =
                          let uu____3869 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3869
                           in
                        let uu____3870 =
                          let uu____3871 =
                            let uu____3872 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3872  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3871
                           in
                        (uu____3868, uu____3870)  in
                      let binary_arith arg_tms2 =
                        let uu____3889 =
                          let uu____3890 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3890
                           in
                        let uu____3891 =
                          let uu____3892 =
                            let uu____3893 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3893  in
                          FStar_SMTEncoding_Term.unboxInt uu____3892  in
                        (uu____3889, uu____3891)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3951 =
                          let uu____3952 = mk_args ts  in op uu____3952  in
                        FStar_All.pipe_right uu____3951 resBox  in
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
                        let uu____4084 =
                          let uu____4089 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4089  in
                        let uu____4098 =
                          let uu____4103 =
                            let uu____4105 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4105  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4103  in
                        mk_bv uu____4084 unary uu____4098 arg_tms2  in
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
                      let uu____4345 =
                        let uu____4355 =
                          FStar_List.tryFind
                            (fun uu____4379  ->
                               match uu____4379 with
                               | (l,uu____4390) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4355 FStar_Util.must  in
                      (match uu____4345 with
                       | (uu____4436,op) ->
                           let uu____4448 = op arg_tms1  in
                           (uu____4448, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___573_4458 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___573_4458.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___573_4458.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___573_4458.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___573_4458.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___573_4458.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___573_4458.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___573_4458.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___573_4458.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___573_4458.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___573_4458.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4460 = encode_term t env1  in
      match uu____4460 with
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
               (uu____4486,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4487;
                             FStar_SMTEncoding_Term.freevars = uu____4488;
                             FStar_SMTEncoding_Term.rng = uu____4489;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4490;
                  FStar_SMTEncoding_Term.freevars = uu____4491;
                  FStar_SMTEncoding_Term.rng = uu____4492;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4538 ->
               let uu____4539 = encode_formula t env1  in
               (match uu____4539 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4559 =
                            let uu____4564 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4564, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4559
                      | uu____4565 ->
                          let uu____4566 =
                            let uu____4577 =
                              let uu____4578 =
                                let uu____4583 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4583, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4578  in
                            ([[valid_tm]], vars, uu____4577)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4566
                       in
                    let ax =
                      let uu____4593 =
                        let uu____4601 =
                          let uu____4603 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4603  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4601)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4593  in
                    let uu____4609 =
                      let uu____4610 =
                        let uu____4613 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4613  in
                      FStar_List.append decls uu____4610  in
                    (tm, uu____4609)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4625 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4625
       then
         let uu____4630 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4632 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4634 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4630 uu____4632
           uu____4634
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4643 ->
           let uu____4666 =
             let uu____4668 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4671 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4673 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4675 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4668
               uu____4671 uu____4673 uu____4675
              in
           failwith uu____4666
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4682 =
             let uu____4684 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4687 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4689 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4691 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4684
               uu____4687 uu____4689 uu____4691
              in
           failwith uu____4682
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4701 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4701
             then
               let uu____4706 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4708 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4706
                 uu____4708
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4714 =
             let uu____4716 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4716
              in
           failwith uu____4714
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4725),uu____4726) ->
           let uu____4775 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4785 -> false  in
           if uu____4775
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4803) ->
           let tv =
             let uu____4809 =
               let uu____4816 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4816
                in
             uu____4809 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4820 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4820
             then
               let uu____4825 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4827 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4825
                 uu____4827
             else ());
            (let t1 =
               let uu____4835 =
                 let uu____4846 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4846]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4835
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4872) ->
           encode_term t1
             (let uu___645_4898 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___645_4898.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___645_4898.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___645_4898.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___645_4898.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___645_4898.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___645_4898.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___645_4898.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___645_4898.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___645_4898.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___645_4898.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4901) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4909 = head_redex env t  in
           if uu____4909
           then let uu____4916 = whnf env t  in encode_term uu____4916 env
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
              let uu____4923 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4947 ->
                      let sym_name =
                        let uu____4958 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4958  in
                      let uu____4961 =
                        let uu____4964 =
                          let uu____4965 =
                            let uu____4973 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4973,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4965  in
                        [uu____4964]  in
                      (uu____4961, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____4980,[]) ->
                      let sym_name =
                        let uu____4985 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4985  in
                      let uu____4988 =
                        let uu____4991 =
                          let uu____4992 =
                            let uu____5000 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____5000,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4992  in
                        [uu____4991]  in
                      (uu____4988, sym_name)
                  | uu____5007 -> ([], "")
                else ([], "")  in
              match uu____4923 with
              | (aux_decls,sym_name) ->
                  let uu____5030 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____5030))
       | FStar_Syntax_Syntax.Tm_type uu____5038 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5040) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5070 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5070 with
            | (binders1,res) ->
                let uu____5081 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5081
                then
                  let uu____5088 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5088 with
                   | (vars,guards_l,env',decls,uu____5113) ->
                       let fsym =
                         let uu____5127 =
                           let uu____5133 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5133, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5127  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5139 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___699_5148 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___699_5148.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___699_5148.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___699_5148.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___699_5148.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___699_5148.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___699_5148.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___699_5148.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___699_5148.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___699_5148.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___699_5148.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___699_5148.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___699_5148.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___699_5148.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___699_5148.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___699_5148.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___699_5148.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___699_5148.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___699_5148.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___699_5148.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___699_5148.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___699_5148.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___699_5148.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___699_5148.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___699_5148.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___699_5148.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___699_5148.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___699_5148.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___699_5148.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___699_5148.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___699_5148.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___699_5148.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___699_5148.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___699_5148.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___699_5148.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___699_5148.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___699_5148.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___699_5148.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___699_5148.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___699_5148.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___699_5148.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___699_5148.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___699_5148.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____5139 with
                        | (pre_opt,res_t) ->
                            let uu____5160 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5160 with
                             | (res_pred,decls') ->
                                 let uu____5171 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5184 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5184, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5188 =
                                         encode_formula pre env'  in
                                       (match uu____5188 with
                                        | (guard,decls0) ->
                                            let uu____5201 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5201, decls0))
                                    in
                                 (match uu____5171 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        FStar_Syntax_Util.is_pure_comp res
                                         in
                                      let t_interp =
                                        let uu____5217 =
                                          let uu____5228 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5228)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____5217
                                         in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t.FStar_Syntax_Syntax.pos f vars
                                            is_pure
                                           in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms)
                                         in
                                      let cvars =
                                        let uu____5250 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5250
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5269 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5271 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5269 <> uu____5271))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1)
                                         in
                                      let prefix1 =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_"  in
                                      let tkey_hash =
                                        let uu____5299 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix1 uu____5299  in
                                      let tsym =
                                        let uu____5303 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix1 uu____5303  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5317 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5317
                                        then
                                          let uu____5320 =
                                            let uu____5322 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5322 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5320
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____5335 =
                                          let uu____5343 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5343)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5335
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5362 =
                                          let uu____5370 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5370,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5362
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
                                        let uu____5387 =
                                          let uu____5395 =
                                            let uu____5396 =
                                              let uu____5407 =
                                                let uu____5408 =
                                                  let uu____5413 =
                                                    let uu____5414 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5414
                                                     in
                                                  (f_has_t, uu____5413)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5408
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5407)
                                               in
                                            let uu____5432 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5432 uu____5396  in
                                          (uu____5395,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5387
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5455 =
                                          let uu____5463 =
                                            let uu____5464 =
                                              let uu____5475 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5475)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5464
                                             in
                                          (uu____5463,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5455
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5498 =
                                        let uu____5499 =
                                          let uu____5502 =
                                            let uu____5505 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5505
                                             in
                                          FStar_List.append decls' uu____5502
                                           in
                                        FStar_List.append decls uu____5499
                                         in
                                      (t1, uu____5498)))))
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
                     let uu____5526 =
                       let uu____5534 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5534,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5526  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5547 =
                       let uu____5555 =
                         let uu____5556 =
                           let uu____5567 =
                             let uu____5568 =
                               let uu____5573 =
                                 let uu____5574 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5574
                                  in
                               (f_has_t, uu____5573)  in
                             FStar_SMTEncoding_Util.mkImp uu____5568  in
                           ([[f_has_t]], [fsym], uu____5567)  in
                         let uu____5600 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5600 uu____5556  in
                       (uu____5555, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5547  in
                   let uu____5617 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5617)))
       | FStar_Syntax_Syntax.Tm_refine uu____5620 ->
           let uu____5627 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5637 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5637 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5646;
                 FStar_Syntax_Syntax.vars = uu____5647;_} ->
                 let uu____5654 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5654 with
                  | (b,f1) ->
                      let uu____5681 =
                        let uu____5682 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5682  in
                      (uu____5681, f1))
             | uu____5699 -> failwith "impossible"  in
           (match uu____5627 with
            | (x,f) ->
                let uu____5717 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5717 with
                 | (base_t,decls) ->
                     let uu____5728 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5728 with
                      | (x1,xtm,env') ->
                          let uu____5745 = encode_formula f env'  in
                          (match uu____5745 with
                           | (refinement,decls') ->
                               let uu____5756 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5756 with
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
                                      let uu____5784 =
                                        let uu____5795 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5806 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5795
                                          uu____5806
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5784
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5860 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5860 <> x1) &&
                                                (let uu____5864 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5864 <> fsym)))
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
                                    ((let uu____5897 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____5897
                                      then
                                        let uu____5901 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____5903 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____5901 tkey_hash uu____5903
                                      else ());
                                     (let tsym =
                                        let uu____5910 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____5910
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
                                        let uu____5930 =
                                          let uu____5938 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____5938)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5930
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
                                        FStar_SMTEncoding_Term.mk_haseq
                                          base_t
                                         in
                                      let t_haseq_ref =
                                        FStar_SMTEncoding_Term.mk_haseq t1
                                         in
                                      let t_haseq1 =
                                        let uu____5958 =
                                          let uu____5966 =
                                            let uu____5967 =
                                              let uu____5978 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____5978)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5967
                                             in
                                          (uu____5966,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5958
                                         in
                                      let t_kinding =
                                        let uu____5992 =
                                          let uu____6000 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6000,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5992
                                         in
                                      let t_interp =
                                        let uu____6014 =
                                          let uu____6022 =
                                            let uu____6023 =
                                              let uu____6034 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6034)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6023
                                             in
                                          (uu____6022,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6014
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1]  in
                                      let uu____6066 =
                                        let uu____6067 =
                                          let uu____6070 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6070
                                           in
                                        FStar_List.append decls uu____6067
                                         in
                                      (t1, uu____6066))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6074) ->
           let ttm =
             let uu____6092 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6092  in
           let uu____6094 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6094 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6106 =
                    let uu____6114 =
                      let uu____6116 =
                        let uu____6118 =
                          let uu____6120 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6120  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6118  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6116
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6114)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6106  in
                let uu____6126 =
                  let uu____6127 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6127  in
                (ttm, uu____6126))
       | FStar_Syntax_Syntax.Tm_app uu____6134 ->
           let uu____6151 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6151 with
            | (head1,args_e) ->
                let uu____6198 =
                  let uu____6213 =
                    let uu____6214 = FStar_Syntax_Subst.compress head1  in
                    uu____6214.FStar_Syntax_Syntax.n  in
                  (uu____6213, args_e)  in
                (match uu____6198 with
                 | uu____6231 when head_redex env head1 ->
                     let uu____6246 = whnf env t  in
                     encode_term uu____6246 env
                 | uu____6247 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6270 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6288) when
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
                       FStar_Syntax_Syntax.pos = uu____6310;
                       FStar_Syntax_Syntax.vars = uu____6311;_},uu____6312),uu____6313)
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
                       FStar_Syntax_Syntax.pos = uu____6339;
                       FStar_Syntax_Syntax.vars = uu____6340;_},uu____6341),
                    (v0,uu____6343)::(v1,uu____6345)::(v2,uu____6347)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6418 = encode_term v0 env  in
                     (match uu____6418 with
                      | (v01,decls0) ->
                          let uu____6429 = encode_term v1 env  in
                          (match uu____6429 with
                           | (v11,decls1) ->
                               let uu____6440 = encode_term v2 env  in
                               (match uu____6440 with
                                | (v21,decls2) ->
                                    let uu____6451 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6451,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6454)::(v1,uu____6456)::(v2,uu____6458)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6525 = encode_term v0 env  in
                     (match uu____6525 with
                      | (v01,decls0) ->
                          let uu____6536 = encode_term v1 env  in
                          (match uu____6536 with
                           | (v11,decls1) ->
                               let uu____6547 = encode_term v2 env  in
                               (match uu____6547 with
                                | (v21,decls2) ->
                                    let uu____6558 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6558,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6560)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6596)::(rng,uu____6598)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6649) ->
                     let e0 =
                       let uu____6671 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6671
                        in
                     ((let uu____6681 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6681
                       then
                         let uu____6686 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6686
                       else ());
                      (let e =
                         let uu____6694 =
                           let uu____6699 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6700 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6699
                             uu____6700
                            in
                         uu____6694 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6709),(arg,uu____6711)::[]) -> encode_term arg env
                 | uu____6746 ->
                     let uu____6761 = encode_args args_e env  in
                     (match uu____6761 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6830 = encode_term head1 env  in
                            match uu____6830 with
                            | (smt_head,decls') ->
                                let app_tm = mk_Apply_args smt_head args  in
                                (match ht_opt with
                                 | uu____6850 ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some
                                     (head_type,formals,c) ->
                                     ((let uu____6919 =
                                         FStar_TypeChecker_Env.debug
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (FStar_Options.Other "PartialApp")
                                          in
                                       if uu____6919
                                       then
                                         let uu____6923 =
                                           FStar_Syntax_Print.term_to_string
                                             head1
                                            in
                                         let uu____6925 =
                                           FStar_Syntax_Print.term_to_string
                                             head_type
                                            in
                                         let uu____6927 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", " formals
                                            in
                                         let uu____6930 =
                                           FStar_Syntax_Print.comp_to_string
                                             c
                                            in
                                         let uu____6932 =
                                           FStar_Syntax_Print.args_to_string
                                             args_e
                                            in
                                         FStar_Util.print5
                                           "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                           uu____6923 uu____6925 uu____6927
                                           uu____6930 uu____6932
                                       else ());
                                      (let uu____6937 =
                                         FStar_Util.first_N
                                           (FStar_List.length args_e) formals
                                          in
                                       match uu____6937 with
                                       | (formals1,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____7035  ->
                                                  fun uu____7036  ->
                                                    match (uu____7035,
                                                            uu____7036)
                                                    with
                                                    | ((bv,uu____7066),
                                                       (a,uu____7068)) ->
                                                        FStar_Syntax_Syntax.NT
                                                          (bv, a)) formals1
                                               args_e
                                              in
                                           let ty =
                                             let uu____7100 =
                                               FStar_Syntax_Util.arrow rest c
                                                in
                                             FStar_All.pipe_right uu____7100
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           ((let uu____7104 =
                                               FStar_TypeChecker_Env.debug
                                                 env.FStar_SMTEncoding_Env.tcenv
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____7104
                                             then
                                               let uu____7108 =
                                                 FStar_Syntax_Print.term_to_string
                                                   ty
                                                  in
                                               FStar_Util.print1
                                                 "Encoding partial application, after subst:\n\tty=%s\n"
                                                 uu____7108
                                             else ());
                                            (let uu____7113 =
                                               let uu____7126 =
                                                 FStar_List.fold_left2
                                                   (fun uu____7161  ->
                                                      fun uu____7162  ->
                                                        fun e  ->
                                                          match (uu____7161,
                                                                  uu____7162)
                                                          with
                                                          | ((t_hyps,decls1),
                                                             (bv,uu____7203))
                                                              ->
                                                              let t1 =
                                                                FStar_Syntax_Subst.subst
                                                                  subst1
                                                                  bv.FStar_Syntax_Syntax.sort
                                                                 in
                                                              let uu____7231
                                                                =
                                                                encode_term_pred
                                                                  FStar_Pervasives_Native.None
                                                                  t1 env e
                                                                 in
                                                              (match uu____7231
                                                               with
                                                               | (t_hyp,decls'1)
                                                                   ->
                                                                   ((
                                                                    let uu____7247
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7247
                                                                    then
                                                                    let uu____7251
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____7253
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7251
                                                                    uu____7253
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                   ([], []) formals1 args
                                                  in
                                               match uu____7126 with
                                               | (t_hyps,decls1) ->
                                                   let uu____7288 =
                                                     match smt_head.FStar_SMTEncoding_Term.tm
                                                     with
                                                     | FStar_SMTEncoding_Term.FreeV
                                                         uu____7297 ->
                                                         encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           head_type env
                                                           smt_head
                                                     | uu____7306 ->
                                                         (FStar_SMTEncoding_Util.mkTrue,
                                                           [])
                                                      in
                                                   (match uu____7288 with
                                                    | (t_head_hyp,decls'1) ->
                                                        let hyp =
                                                          FStar_SMTEncoding_Term.mk_and_l
                                                            (t_head_hyp ::
                                                            t_hyps)
                                                            FStar_Range.dummyRange
                                                           in
                                                        let uu____7322 =
                                                          encode_term_pred
                                                            FStar_Pervasives_Native.None
                                                            ty env app_tm
                                                           in
                                                        (match uu____7322
                                                         with
                                                         | (has_type_conclusion,decls'')
                                                             ->
                                                             let has_type =
                                                               FStar_SMTEncoding_Util.mkImp
                                                                 (hyp,
                                                                   has_type_conclusion)
                                                                in
                                                             let cvars =
                                                               FStar_SMTEncoding_Term.free_variables
                                                                 has_type
                                                                in
                                                             let app_tm_vars
                                                               =
                                                               FStar_SMTEncoding_Term.free_variables
                                                                 app_tm
                                                                in
                                                             let uu____7344 =
                                                               let uu____7351
                                                                 =
                                                                 FStar_SMTEncoding_Term.fvs_subset_of
                                                                   cvars
                                                                   app_tm_vars
                                                                  in
                                                               if uu____7351
                                                               then
                                                                 ([app_tm],
                                                                   app_tm_vars)
                                                               else
                                                                 (let uu____7364
                                                                    =
                                                                    let uu____7366
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7366
                                                                     in
                                                                  if
                                                                    uu____7364
                                                                  then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                  else
                                                                    (
                                                                    (
                                                                    let uu____7379
                                                                    =
                                                                    let uu____7385
                                                                    =
                                                                    let uu____7387
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7387
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7385)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7379);
                                                                    ([],
                                                                    cvars)))
                                                                in
                                                             (match uu____7344
                                                              with
                                                              | (pattern,vars)
                                                                  ->
                                                                  (vars,
                                                                    pattern,
                                                                    has_type,
                                                                    (
                                                                    FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls''))))))
                                                in
                                             match uu____7113 with
                                             | (vars,pattern,has_type,decls'')
                                                 ->
                                                 ((let uu____7434 =
                                                     FStar_TypeChecker_Env.debug
                                                       env.FStar_SMTEncoding_Env.tcenv
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____7434
                                                   then
                                                     let uu____7438 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         has_type
                                                        in
                                                     FStar_Util.print1
                                                       "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                       uu____7438
                                                   else ());
                                                  (let tkey_hash =
                                                     FStar_SMTEncoding_Term.hash_of_term
                                                       app_tm
                                                      in
                                                   let e_typing =
                                                     let uu____7446 =
                                                       let uu____7454 =
                                                         FStar_SMTEncoding_Term.mkForall
                                                           t0.FStar_Syntax_Syntax.pos
                                                           ([pattern], vars,
                                                             has_type)
                                                          in
                                                       let uu____7463 =
                                                         let uu____7465 =
                                                           let uu____7467 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm
                                                              in
                                                           FStar_Util.digest_of_string
                                                             uu____7467
                                                            in
                                                         Prims.op_Hat
                                                           "partial_app_typing_"
                                                           uu____7465
                                                          in
                                                       (uu____7454,
                                                         (FStar_Pervasives_Native.Some
                                                            "Partial app typing"),
                                                         uu____7463)
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____7446
                                                      in
                                                   let uu____7473 =
                                                     let uu____7476 =
                                                       let uu____7479 =
                                                         let uu____7482 =
                                                           FStar_SMTEncoding_Term.mk_decls
                                                             "" tkey_hash
                                                             [e_typing]
                                                             (FStar_List.append
                                                                decls
                                                                (FStar_List.append
                                                                   decls'
                                                                   decls''))
                                                            in
                                                         FStar_List.append
                                                           decls'' uu____7482
                                                          in
                                                       FStar_List.append
                                                         decls' uu____7479
                                                        in
                                                     FStar_List.append decls
                                                       uu____7476
                                                      in
                                                   (app_tm, uu____7473))))))))
                             in
                          let encode_full_app fv =
                            let uu____7502 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____7502 with
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
                                   FStar_Syntax_Syntax.pos = uu____7545;
                                   FStar_Syntax_Syntax.vars = uu____7546;_},uu____7547)
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
                                   FStar_Syntax_Syntax.pos = uu____7554;
                                   FStar_Syntax_Syntax.vars = uu____7555;_},uu____7556)
                                ->
                                let uu____7561 =
                                  let uu____7562 =
                                    let uu____7567 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7567
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7562
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7561
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7597 =
                                  let uu____7598 =
                                    let uu____7603 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7603
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7598
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7597
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7632,(FStar_Util.Inl t1,uu____7634),uu____7635)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7682,(FStar_Util.Inr c,uu____7684),uu____7685)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7732 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let uu____7756 =
                                 let head_type2 =
                                   let uu____7778 =
                                     FStar_TypeChecker_Normalize.normalize_refinement
                                       [FStar_TypeChecker_Env.Weak;
                                       FStar_TypeChecker_Env.HNF;
                                       FStar_TypeChecker_Env.EraseUniverses]
                                       env.FStar_SMTEncoding_Env.tcenv
                                       head_type1
                                      in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.unrefine uu____7778
                                    in
                                 let uu____7781 =
                                   curried_arrow_formals_comp head_type2  in
                                 match uu____7781 with
                                 | (formals,c) ->
                                     if
                                       (FStar_List.length formals) <
                                         (FStar_List.length args)
                                     then
                                       let head_type3 =
                                         let uu____7832 =
                                           FStar_TypeChecker_Normalize.normalize_refinement
                                             [FStar_TypeChecker_Env.Weak;
                                             FStar_TypeChecker_Env.HNF;
                                             FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.UnfoldUntil
                                               FStar_Syntax_Syntax.delta_constant]
                                             env.FStar_SMTEncoding_Env.tcenv
                                             head_type2
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.unrefine
                                           uu____7832
                                          in
                                       let uu____7833 =
                                         curried_arrow_formals_comp
                                           head_type3
                                          in
                                       (match uu____7833 with
                                        | (formals1,c1) ->
                                            (head_type3, formals1, c1))
                                     else (head_type2, formals, c)
                                  in
                               (match uu____7756 with
                                | (head_type2,formals,c) ->
                                    ((let uu____7916 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "PartialApp")
                                         in
                                      if uu____7916
                                      then
                                        let uu____7920 =
                                          FStar_Syntax_Print.term_to_string
                                            head_type2
                                           in
                                        let uu____7922 =
                                          FStar_Syntax_Print.binders_to_string
                                            ", " formals
                                           in
                                        let uu____7925 =
                                          FStar_Syntax_Print.args_to_string
                                            args_e
                                           in
                                        FStar_Util.print3
                                          "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                          uu____7920 uu____7922 uu____7925
                                      else ());
                                     (match head2.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.pos =
                                               uu____7935;
                                             FStar_Syntax_Syntax.vars =
                                               uu____7936;_},uu____7937)
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
                                      | uu____7955 ->
                                          if
                                            (FStar_List.length formals) >
                                              (FStar_List.length args)
                                          then
                                            encode_partial_app
                                              (FStar_Pervasives_Native.Some
                                                 (head_type2, formals, c))
                                          else
                                            encode_partial_app
                                              FStar_Pervasives_Native.None)))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8044 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8044 with
            | (bs1,body1,opening) ->
                let fallback uu____8067 =
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
                  let uu____8077 =
                    let uu____8078 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8078
                     in
                  let uu____8080 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8077, uu____8080)  in
                let is_impure rc =
                  let uu____8090 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8090 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8105 =
                          let uu____8118 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8118
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8105 with
                         | (t1,uu____8121,uu____8122) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8140 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8140
                  then
                    let uu____8145 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8145
                  else
                    (let uu____8148 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8148
                     then
                       let uu____8153 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8153
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8161 =
                         let uu____8167 =
                           let uu____8169 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8169
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8167)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8161);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8174 =
                       (is_impure rc) &&
                         (let uu____8177 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8177)
                        in
                     if uu____8174
                     then fallback ()
                     else
                       (let uu____8186 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8186 with
                        | (vars,guards,envbody,decls,uu____8211) ->
                            let body2 =
                              let uu____8225 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8225
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____8230 = encode_term body2 envbody  in
                            (match uu____8230 with
                             | (body3,decls') ->
                                 let uu____8241 =
                                   let uu____8250 = codomain_eff rc  in
                                   match uu____8250 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8269 = encode_term tfun env
                                          in
                                       (match uu____8269 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8241 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8303 =
                                          let uu____8314 =
                                            let uu____8315 =
                                              let uu____8320 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8320, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8315
                                             in
                                          ([], vars, uu____8314)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8303
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8328 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8368 =
                                              let uu____8379 =
                                                let uu____8390 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____8390
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8379
                                               in
                                            let uu____8417 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____8368, uu____8417)
                                         in
                                      (match uu____8328 with
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
                                           ((let uu____8464 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8464
                                             then
                                               let uu____8469 =
                                                 let uu____8471 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8471
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8481 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8469 uu____8481
                                             else ());
                                            (let uu____8486 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8486 with
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 ((let uu____8495 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8495
                                                   then
                                                     let uu____8500 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t1
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8500
                                                   else ());
                                                  (let decls1 =
                                                     FStar_List.append decls
                                                       (FStar_List.append
                                                          decls' decls'')
                                                      in
                                                   (t1, decls1)))
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 let cvar_sorts =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_sort
                                                     cvars1
                                                    in
                                                 let fsym =
                                                   let uu____8521 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8521
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8530 =
                                                     let uu____8538 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8538)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8530
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
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
                                                       let uu____8555 =
                                                         let uu____8556 =
                                                           let uu____8564 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8564,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8556
                                                          in
                                                       [uu____8555]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8579 =
                                                     let uu____8587 =
                                                       let uu____8588 =
                                                         let uu____8599 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8599)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8588
                                                        in
                                                     (uu____8587,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8579
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8613 =
                                                   let uu____8614 =
                                                     let uu____8617 =
                                                       let uu____8620 =
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
                                                         decls'' uu____8620
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8617
                                                      in
                                                   FStar_List.append decls
                                                     uu____8614
                                                    in
                                                 (f, uu____8613)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8623,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8624;
                          FStar_Syntax_Syntax.lbunivs = uu____8625;
                          FStar_Syntax_Syntax.lbtyp = uu____8626;
                          FStar_Syntax_Syntax.lbeff = uu____8627;
                          FStar_Syntax_Syntax.lbdef = uu____8628;
                          FStar_Syntax_Syntax.lbattrs = uu____8629;
                          FStar_Syntax_Syntax.lbpos = uu____8630;_}::uu____8631),uu____8632)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8666;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8668;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8670;
                FStar_Syntax_Syntax.lbpos = uu____8671;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8698 ->
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
              let uu____8770 =
                let uu____8775 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8775 env  in
              match uu____8770 with
              | (ee1,decls1) ->
                  let uu____8800 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8800 with
                   | (xs,e21) ->
                       let uu____8825 = FStar_List.hd xs  in
                       (match uu____8825 with
                        | (x1,uu____8843) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____8849 = encode_body e21 env'  in
                            (match uu____8849 with
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
            let uu____8879 =
              let uu____8887 =
                let uu____8888 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8888  in
              FStar_SMTEncoding_Env.gen_term_var env uu____8887  in
            match uu____8879 with
            | (scrsym,scr',env1) ->
                let uu____8898 = encode_term e env1  in
                (match uu____8898 with
                 | (scr,decls) ->
                     let uu____8909 =
                       let encode_branch b uu____8938 =
                         match uu____8938 with
                         | (else_case,decls1) ->
                             let uu____8957 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8957 with
                              | (p,w,br) ->
                                  let uu____8983 = encode_pat env1 p  in
                                  (match uu____8983 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9020  ->
                                                   match uu____9020 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9027 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9049 =
                                               encode_term w1 env2  in
                                             (match uu____9049 with
                                              | (w2,decls2) ->
                                                  let uu____9062 =
                                                    let uu____9063 =
                                                      let uu____9068 =
                                                        let uu____9069 =
                                                          let uu____9074 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9074)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9069
                                                         in
                                                      (guard, uu____9068)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9063
                                                     in
                                                  (uu____9062, decls2))
                                          in
                                       (match uu____9027 with
                                        | (guard1,decls2) ->
                                            let uu____9089 =
                                              encode_br br env2  in
                                            (match uu____9089 with
                                             | (br1,decls3) ->
                                                 let uu____9102 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9102,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8909 with
                      | (match_tm,decls1) ->
                          let uu____9123 =
                            let uu____9124 =
                              let uu____9135 =
                                let uu____9142 =
                                  let uu____9147 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9147, scr)  in
                                [uu____9142]  in
                              (uu____9135, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9124
                              FStar_Range.dummyRange
                             in
                          (uu____9123, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9170 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9170
       then
         let uu____9173 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9173
       else ());
      (let uu____9178 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9178 with
       | (vars,pat_term) ->
           let uu____9195 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9237  ->
                     fun v1  ->
                       match uu____9237 with
                       | (env1,vars1) ->
                           let uu____9273 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____9273 with
                            | (xx,uu____9292,env2) ->
                                let uu____9296 =
                                  let uu____9303 =
                                    let uu____9308 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____9308)  in
                                  uu____9303 :: vars1  in
                                (env2, uu____9296))) (env, []))
              in
           (match uu____9195 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9363 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9364 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9365 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9373 = encode_const c env1  in
                      (match uu____9373 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9381::uu____9382 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9386 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9409 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9409 with
                        | (uu____9417,uu____9418::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9423 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9459  ->
                                  match uu____9459 with
                                  | (arg,uu____9469) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9478 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9478))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9510) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9541 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9566 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9612  ->
                                  match uu____9612 with
                                  | (arg,uu____9628) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9637 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9637))
                         in
                      FStar_All.pipe_right uu____9566 FStar_List.flatten
                   in
                let pat_term1 uu____9668 = encode_term pat_term env1  in
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
      let uu____9678 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9726  ->
                fun uu____9727  ->
                  match (uu____9726, uu____9727) with
                  | ((tms,decls),(t,uu____9767)) ->
                      let uu____9794 = encode_term t env  in
                      (match uu____9794 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9678 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____9872  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1339_9881 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1339_9881.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1339_9881.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1339_9881.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1339_9881.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1339_9881.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1339_9881.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1339_9881.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1339_9881.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1339_9881.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1339_9881.FStar_SMTEncoding_Env.global_cache)
        }  in
      encode_formula quant env1

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1344_9898 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1344_9898.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1344_9898.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1344_9898.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1344_9898.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1344_9898.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1344_9898.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1344_9898.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1344_9898.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1344_9898.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1344_9898.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9914 = FStar_Syntax_Util.head_and_args t  in
        match uu____9914 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9977::(x,uu____9979)::(t1,uu____9981)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10048 = encode_term x env1  in
                 (match uu____10048 with
                  | (x1,decls) ->
                      let uu____10059 = encode_term t1 env1  in
                      (match uu____10059 with
                       | (t2,decls') ->
                           let uu____10070 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10070, (FStar_List.append decls decls'))))
             | uu____10071 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10114  ->
             match uu____10114 with
             | (pats_l1,decls) ->
                 let uu____10159 =
                   FStar_List.fold_right
                     (fun uu____10194  ->
                        fun uu____10195  ->
                          match (uu____10194, uu____10195) with
                          | ((p,uu____10237),(pats1,decls1)) ->
                              let uu____10272 = encode_smt_pattern p  in
                              (match uu____10272 with
                               | (t,d) ->
                                   let uu____10287 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10287 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10304 =
                                            let uu____10310 =
                                              let uu____10312 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10314 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10312 uu____10314
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10310)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10304);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10159 with
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
        let uu____10374 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10374
        then
          let uu____10379 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10381 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10379 uu____10381
        else ()  in
      let enc f r l =
        let uu____10423 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10455 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10455 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10423 with
        | (decls,args) ->
            let uu____10486 =
              let uu___1408_10487 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1408_10487.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1408_10487.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10486, decls)
         in
      let const_op f r uu____10522 =
        let uu____10535 = f r  in (uu____10535, [])  in
      let un_op f l =
        let uu____10558 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10558  in
      let bin_op f uu___2_10578 =
        match uu___2_10578 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10589 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10630 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10655  ->
                 match uu____10655 with
                 | (t,uu____10671) ->
                     let uu____10676 = encode_formula t env  in
                     (match uu____10676 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10630 with
        | (decls,phis) ->
            let uu____10705 =
              let uu___1438_10706 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1438_10706.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1438_10706.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10705, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10769  ->
               match uu____10769 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10790) -> false
                    | uu____10793 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10812 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10812
        else
          (let uu____10829 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10829 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10897 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10929 =
                       let uu____10934 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10935 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10934, uu____10935)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10929
                 | uu____10936 -> failwith "Impossible")
             in
          uu____10897 r args
        else
          (let uu____10942 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10942)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11004 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11036 =
                       let uu____11041 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11042 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11041, uu____11042)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11036
                 | uu____11043 -> failwith "Impossible")
             in
          uu____11004 r args
        else
          (let uu____11049 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11049)
         in
      let mk_imp1 r uu___3_11078 =
        match uu___3_11078 with
        | (lhs,uu____11084)::(rhs,uu____11086)::[] ->
            let uu____11127 = encode_formula rhs env  in
            (match uu____11127 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11142) ->
                      (l1, decls1)
                  | uu____11147 ->
                      let uu____11148 = encode_formula lhs env  in
                      (match uu____11148 with
                       | (l2,decls2) ->
                           let uu____11159 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11159, (FStar_List.append decls1 decls2)))))
        | uu____11160 -> failwith "impossible"  in
      let mk_ite r uu___4_11188 =
        match uu___4_11188 with
        | (guard,uu____11194)::(_then,uu____11196)::(_else,uu____11198)::[]
            ->
            let uu____11255 = encode_formula guard env  in
            (match uu____11255 with
             | (g,decls1) ->
                 let uu____11266 = encode_formula _then env  in
                 (match uu____11266 with
                  | (t,decls2) ->
                      let uu____11277 = encode_formula _else env  in
                      (match uu____11277 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11289 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11319 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11319  in
      let connectives =
        let uu____11349 =
          let uu____11374 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11374)  in
        let uu____11417 =
          let uu____11444 =
            let uu____11469 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11469)  in
          let uu____11512 =
            let uu____11539 =
              let uu____11566 =
                let uu____11591 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11591)  in
              let uu____11634 =
                let uu____11661 =
                  let uu____11688 =
                    let uu____11713 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11713)  in
                  [uu____11688;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11661  in
              uu____11566 :: uu____11634  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11539  in
          uu____11444 :: uu____11512  in
        uu____11349 :: uu____11417  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12258 = encode_formula phi' env  in
            (match uu____12258 with
             | (phi2,decls) ->
                 let uu____12269 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12269, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12271 ->
            let uu____12278 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12278 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12317 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12317 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12329;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12331;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12333;
                 FStar_Syntax_Syntax.lbpos = uu____12334;_}::[]),e2)
            ->
            let uu____12361 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12361 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12414::(x,uu____12416)::(t,uu____12418)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12485 = encode_term x env  in
                 (match uu____12485 with
                  | (x1,decls) ->
                      let uu____12496 = encode_term t env  in
                      (match uu____12496 with
                       | (t1,decls') ->
                           let uu____12507 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12507, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12510)::(msg,uu____12512)::(phi2,uu____12514)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12581 =
                   let uu____12586 =
                     let uu____12587 = FStar_Syntax_Subst.compress r  in
                     uu____12587.FStar_Syntax_Syntax.n  in
                   let uu____12590 =
                     let uu____12591 = FStar_Syntax_Subst.compress msg  in
                     uu____12591.FStar_Syntax_Syntax.n  in
                   (uu____12586, uu____12590)  in
                 (match uu____12581 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12600))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12611 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12618)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12653 when head_redex env head2 ->
                 let uu____12668 = whnf env phi1  in
                 encode_formula uu____12668 env
             | uu____12669 ->
                 let uu____12684 = encode_term phi1 env  in
                 (match uu____12684 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12696 =
                          let uu____12698 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12699 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12698 uu____12699
                           in
                        if uu____12696
                        then tt
                        else
                          (let uu___1625_12703 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___1625_12703.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___1625_12703.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12704 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12704, decls)))
        | uu____12705 ->
            let uu____12706 = encode_term phi1 env  in
            (match uu____12706 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12718 =
                     let uu____12720 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12721 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12720 uu____12721  in
                   if uu____12718
                   then tt
                   else
                     (let uu___1633_12725 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1633_12725.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1633_12725.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12726 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12726, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12770 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12770 with
        | (vars,guards,env2,decls,uu____12809) ->
            let uu____12822 = encode_smt_patterns ps env2  in
            (match uu____12822 with
             | (pats,decls') ->
                 let uu____12859 = encode_formula body env2  in
                 (match uu____12859 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12891;
                             FStar_SMTEncoding_Term.rng = uu____12892;_}::[])::[]
                            when
                            let uu____12912 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12912 = gf -> []
                        | uu____12915 -> guards  in
                      let uu____12920 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12920, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12931 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12931 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12940 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13046  ->
                     match uu____13046 with
                     | (l,uu____13071) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12940 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13140,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13232 = encode_q_body env vars pats body  in
             match uu____13232 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13277 =
                     let uu____13288 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13288)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13277
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13319 = encode_q_body env vars pats body  in
             match uu____13319 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13363 =
                   let uu____13364 =
                     let uu____13375 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13375)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13364
                    in
                 (uu____13363, decls))))
