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
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____292 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____312;
             FStar_Syntax_Syntax.vars = uu____313;_},uu____314)
          ->
          let uu____339 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____339 FStar_Option.isNone
      | uu____358 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____372 =
        let uu____373 = FStar_Syntax_Util.un_uinst t  in
        uu____373.FStar_Syntax_Syntax.n  in
      match uu____372 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____377,uu____378,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_403  ->
                  match uu___0_403 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____406 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____409 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | uu____428 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____441 = head_normal env t  in
      if uu____441
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Eager_unfolding true;
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
        FStar_TypeChecker_Env.Eager_unfolding true;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____465 =
      let uu____466 = FStar_Syntax_Syntax.null_binder t  in [uu____466]  in
    let uu____485 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____465 uu____485 FStar_Pervasives_Native.None
  
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
                let uu____507 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____507 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____508 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____508
                | s ->
                    let uu____511 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____511) e)
  
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
          let uu____567 =
            let uu____573 =
              let uu____575 = FStar_Util.string_of_int arity  in
              let uu____577 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____575 uu____577
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____573)  in
          FStar_Errors.raise_error uu____567 rng
  
let (isTotFun_axioms :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.fvs ->
        FStar_SMTEncoding_Term.term Prims.list ->
          Prims.bool -> FStar_SMTEncoding_Term.term)
  =
  fun pos  ->
    fun head1  ->
      fun vars  ->
        fun guards  ->
          fun is_pure  ->
            let maybe_mkForall pat vars1 body =
              match vars1 with
              | [] -> body
              | uu____665 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body)
               in
            let rec is_tot_fun_axioms ctx ctx_guard head2 vars1 guards1 =
              match (vars1, guards1) with
              | ([],[]) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____782::[],uu____783) ->
                  if is_pure
                  then
                    let uu____823 =
                      let uu____824 =
                        let uu____829 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2  in
                        (ctx_guard, uu____829)  in
                      FStar_SMTEncoding_Util.mkImp uu____824  in
                    maybe_mkForall [[head2]] ctx uu____823
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2,g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____881 =
                      let uu____882 =
                        let uu____887 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2  in
                        (ctx_guard, uu____887)  in
                      FStar_SMTEncoding_Util.mkImp uu____882  in
                    maybe_mkForall [[head2]] ctx uu____881  in
                  let app = mk_Apply head2 [x]  in
                  let ctx1 = FStar_List.append ctx [x]  in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x)  in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2  in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
               in
            is_tot_fun_axioms [] FStar_SMTEncoding_Util.mkTrue head1 vars
              guards
  
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
                  (let uu____999 = FStar_Util.first_N arity args  in
                   match uu____999 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1023 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____1023 arity n_args rng)
  
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
          let uu____1046 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____1046 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1055  ->
    match uu___1_1055 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1061 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1109;
                       FStar_SMTEncoding_Term.rng = uu____1110;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1141) ->
              let uu____1151 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1168 -> false) args (FStar_List.rev xs))
                 in
              if uu____1151
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f  in
                ((let uu____1177 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp")
                     in
                  if uu____1177
                  then
                    let uu____1182 = FStar_SMTEncoding_Term.print_smt_term t
                       in
                    let uu____1184 =
                      match n1 with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x
                       in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1182 uu____1184
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1194,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1198 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1206 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1206))
                 in
              if uu____1198
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1213 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____1231 'Auu____1232 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1231) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1232) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1290  ->
                  match uu____1290 with
                  | (x,uu____1296) ->
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
              let uu____1304 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1316 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1316) uu____1304 tl1
               in
            let uu____1319 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1346  ->
                      match uu____1346 with
                      | (b,uu____1353) ->
                          let uu____1354 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1354))
               in
            (match uu____1319 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1361) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____1375 =
                   let uu____1381 =
                     let uu____1383 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1383
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1381)  in
                 FStar_Errors.log_issue pos uu____1375)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1669 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1684 ->
            let uu____1691 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1691
        | uu____1693 ->
            if norm1
            then let uu____1695 = whnf env t1  in aux false uu____1695
            else
              (let uu____1699 =
                 let uu____1701 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1703 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1701 uu____1703
                  in
               failwith uu____1699)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1745) ->
        let uu____1750 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1750 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1771 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1771)
              | uu____1778 -> (args, res)))
    | uu____1779 ->
        let uu____1780 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1780)
  
let is_arithmetic_primitive :
  'Auu____1794 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1794 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1817::uu____1818::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1822::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1825 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1856 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1879 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1889 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1889)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1931)::uu____1932::uu____1933::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1984)::uu____1985::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2022 -> false
  
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
          let uu____2346 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2346, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2348 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2348, [])
      | FStar_Const.Const_char c1 ->
          let uu____2351 =
            let uu____2352 =
              let uu____2360 =
                let uu____2363 =
                  let uu____2364 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2364  in
                [uu____2363]  in
              ("FStar.Char.__char_of_int", uu____2360)  in
            FStar_SMTEncoding_Util.mkApp uu____2352  in
          (uu____2351, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2382 =
            let uu____2383 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2383  in
          (uu____2382, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2404) ->
          let uu____2407 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2407, [])
      | FStar_Const.Const_range uu____2408 ->
          let uu____2409 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2409, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2412 =
            let uu____2413 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2413  in
          (uu____2412, [])
      | c1 ->
          let uu____2415 =
            let uu____2417 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2417  in
          failwith uu____2415

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
        (let uu____2446 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2446
         then
           let uu____2449 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2449
         else ());
        (let uu____2455 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2537  ->
                   fun b  ->
                     match uu____2537 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2602 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2618 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2618 with
                           | (xxsym,xx,env') ->
                               let uu____2643 =
                                 let uu____2648 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2648 env1 xx
                                  in
                               (match uu____2643 with
                                | (guard_x_t,decls') ->
                                    let uu____2663 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2663, guard_x_t, env', decls', x))
                            in
                         (match uu____2602 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2455 with
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
          let uu____2763 = encode_term t env  in
          match uu____2763 with
          | (t1,decls) ->
              let uu____2774 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2774, decls)

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
          let uu____2785 = encode_term t env  in
          match uu____2785 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2800 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2800, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2802 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2802, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2808 = encode_args args_e env  in
        match uu____2808 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2827 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2849 = FStar_List.hd arg_tms1  in unbox uu____2849
               in
            let binary unbox arg_tms1 =
              let uu____2874 =
                let uu____2875 = FStar_List.hd arg_tms1  in unbox uu____2875
                 in
              let uu____2876 =
                let uu____2877 =
                  let uu____2878 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2878  in
                unbox uu____2877  in
              (uu____2874, uu____2876)  in
            let mk_default uu____2886 =
              let uu____2887 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2887 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2976 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2976
              then
                let uu____2979 =
                  let uu____2980 = mk_args ts  in op uu____2980  in
                FStar_All.pipe_right uu____2979 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____3038 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3038
              then
                let uu____3041 = binary unbox ts  in
                match uu____3041 with
                | (t1,t2) ->
                    let uu____3048 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3048 box
              else
                (let uu____3054 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3054
                 then
                   let uu____3057 =
                     let uu____3058 = binary unbox ts  in op uu____3058  in
                   FStar_All.pipe_right uu____3057 box
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
            let uu____3493 =
              let uu____3503 =
                FStar_List.tryFind
                  (fun uu____3527  ->
                     match uu____3527 with
                     | (l,uu____3538) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3503 FStar_Util.must  in
            (match uu____3493 with
             | (uu____3582,op) ->
                 let uu____3594 = op arg_tms  in (uu____3594, decls))

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
        let uu____3610 = FStar_List.hd args_e  in
        match uu____3610 with
        | (tm_sz,uu____3626) ->
            let uu____3635 = uu____3610  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3646 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3672::(sz_arg,uu____3674)::uu____3675::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3742 =
                    let uu____3743 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3743  in
                  let uu____3770 =
                    let uu____3774 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3774  in
                  (uu____3742, uu____3770)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3781::(sz_arg,uu____3783)::uu____3784::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3851 =
                    let uu____3853 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3853
                     in
                  failwith uu____3851
              | uu____3863 ->
                  let uu____3878 = FStar_List.tail args_e  in
                  (uu____3878, FStar_Pervasives_Native.None)
               in
            (match uu____3646 with
             | (arg_tms,ext_sz) ->
                 let uu____3905 = encode_args arg_tms env  in
                 (match uu____3905 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3926 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3938 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3938  in
                      let unary_arith arg_tms2 =
                        let uu____3949 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3949  in
                      let binary arg_tms2 =
                        let uu____3964 =
                          let uu____3965 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3965
                           in
                        let uu____3966 =
                          let uu____3967 =
                            let uu____3968 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3968  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3967
                           in
                        (uu____3964, uu____3966)  in
                      let binary_arith arg_tms2 =
                        let uu____3985 =
                          let uu____3986 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3986
                           in
                        let uu____3987 =
                          let uu____3988 =
                            let uu____3989 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3989  in
                          FStar_SMTEncoding_Term.unboxInt uu____3988  in
                        (uu____3985, uu____3987)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____4047 =
                          let uu____4048 = mk_args ts  in op uu____4048  in
                        FStar_All.pipe_right uu____4047 resBox  in
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
                        let uu____4180 =
                          let uu____4185 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4185  in
                        let uu____4194 =
                          let uu____4199 =
                            let uu____4201 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4201  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4199  in
                        mk_bv uu____4180 unary uu____4194 arg_tms2  in
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
                      let uu____4441 =
                        let uu____4451 =
                          FStar_List.tryFind
                            (fun uu____4475  ->
                               match uu____4475 with
                               | (l,uu____4486) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4451 FStar_Util.must  in
                      (match uu____4441 with
                       | (uu____4532,op) ->
                           let uu____4544 = op arg_tms1  in
                           (uu____4544, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___586_4554 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___586_4554.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___586_4554.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___586_4554.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___586_4554.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___586_4554.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___586_4554.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___586_4554.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___586_4554.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___586_4554.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___586_4554.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4556 = encode_term t env1  in
      match uu____4556 with
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
               (uu____4582,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4583;
                             FStar_SMTEncoding_Term.freevars = uu____4584;
                             FStar_SMTEncoding_Term.rng = uu____4585;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4586;
                  FStar_SMTEncoding_Term.freevars = uu____4587;
                  FStar_SMTEncoding_Term.rng = uu____4588;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4634 ->
               let uu____4635 = encode_formula t env1  in
               (match uu____4635 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4655 =
                            let uu____4660 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4660, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4655
                      | uu____4661 ->
                          let uu____4662 =
                            let uu____4673 =
                              let uu____4674 =
                                let uu____4679 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4679, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4674  in
                            ([[valid_tm]], vars, uu____4673)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4662
                       in
                    let ax =
                      let uu____4689 =
                        let uu____4697 =
                          let uu____4699 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4699  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4697)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4689  in
                    let uu____4705 =
                      let uu____4706 =
                        let uu____4709 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4709  in
                      FStar_List.append decls uu____4706  in
                    (tm, uu____4705)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4721 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4721
       then
         let uu____4726 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4728 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4730 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4726 uu____4728
           uu____4730
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4739 ->
           let uu____4762 =
             let uu____4764 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4767 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4769 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4771 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4764
               uu____4767 uu____4769 uu____4771
              in
           failwith uu____4762
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4778 =
             let uu____4780 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4783 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4785 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4787 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4780
               uu____4783 uu____4785 uu____4787
              in
           failwith uu____4778
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4797 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4797
             then
               let uu____4802 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4804 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4802
                 uu____4804
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4810 =
             let uu____4812 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4812
              in
           failwith uu____4810
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4821),uu____4822) ->
           let uu____4871 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4881 -> false  in
           if uu____4871
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4899) ->
           let tv =
             let uu____4905 =
               let uu____4912 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4912
                in
             uu____4905 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4916 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4916
             then
               let uu____4921 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4923 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4921
                 uu____4923
             else ());
            (let t1 =
               let uu____4931 =
                 let uu____4942 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4942]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4931
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4968) ->
           encode_term t1
             (let uu___658_4994 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___658_4994.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___658_4994.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___658_4994.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___658_4994.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___658_4994.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___658_4994.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___658_4994.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___658_4994.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___658_4994.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___658_4994.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4997) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5005 = head_redex env t  in
           if uu____5005
           then let uu____5012 = whnf env t  in encode_term uu____5012 env
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
              let uu____5019 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____5043 ->
                      let sym_name =
                        let uu____5054 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____5054  in
                      let uu____5057 =
                        let uu____5060 =
                          let uu____5061 =
                            let uu____5069 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____5069,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____5061  in
                        [uu____5060]  in
                      (uu____5057, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____5076,[]) ->
                      let sym_name =
                        let uu____5081 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____5081  in
                      let uu____5084 =
                        let uu____5087 =
                          let uu____5088 =
                            let uu____5096 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____5096,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____5088  in
                        [uu____5087]  in
                      (uu____5084, sym_name)
                  | uu____5103 -> ([], "")
                else ([], "")  in
              match uu____5019 with
              | (aux_decls,sym_name) ->
                  let uu____5126 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____5126))
       | FStar_Syntax_Syntax.Tm_type uu____5134 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5136) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5166 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5166 with
            | (binders1,res) ->
                let uu____5177 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5177
                then
                  let uu____5184 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5184 with
                   | (vars,guards_l,env',decls,uu____5209) ->
                       let fsym =
                         let uu____5223 =
                           let uu____5229 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5229, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5223  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5235 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___712_5244 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___712_5244.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___712_5244.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___712_5244.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___712_5244.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___712_5244.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___712_5244.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___712_5244.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___712_5244.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___712_5244.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___712_5244.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___712_5244.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___712_5244.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___712_5244.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___712_5244.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___712_5244.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___712_5244.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___712_5244.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___712_5244.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___712_5244.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___712_5244.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___712_5244.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___712_5244.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___712_5244.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___712_5244.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___712_5244.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___712_5244.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___712_5244.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___712_5244.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___712_5244.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___712_5244.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___712_5244.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___712_5244.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___712_5244.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___712_5244.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___712_5244.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___712_5244.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___712_5244.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___712_5244.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___712_5244.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___712_5244.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___712_5244.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___712_5244.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____5235 with
                        | (pre_opt,res_t) ->
                            let uu____5256 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5256 with
                             | (res_pred,decls') ->
                                 let uu____5267 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5280 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5280, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5284 =
                                         encode_formula pre env'  in
                                       (match uu____5284 with
                                        | (guard,decls0) ->
                                            let uu____5297 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5297, decls0))
                                    in
                                 (match uu____5267 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        let uu____5312 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv)
                                           in
                                        FStar_All.pipe_right uu____5312
                                          FStar_Syntax_Util.is_pure_comp
                                         in
                                      let t_interp =
                                        let uu____5321 =
                                          let uu____5332 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5332)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____5321
                                         in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure
                                           in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms)
                                         in
                                      let cvars =
                                        let uu____5354 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5354
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5373 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5375 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5373 <> uu____5375))
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
                                        let uu____5403 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix1 uu____5403  in
                                      let tsym =
                                        let uu____5407 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix1 uu____5407  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5421 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5421
                                        then
                                          let uu____5424 =
                                            let uu____5426 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5426 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5424
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____5439 =
                                          let uu____5447 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5447)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5439
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5466 =
                                          let uu____5474 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5474,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5466
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
                                        let uu____5491 =
                                          let uu____5499 =
                                            let uu____5500 =
                                              let uu____5511 =
                                                let uu____5512 =
                                                  let uu____5517 =
                                                    let uu____5518 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5518
                                                     in
                                                  (f_has_t, uu____5517)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5512
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5511)
                                               in
                                            let uu____5536 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5536 uu____5500  in
                                          (uu____5499,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5491
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5559 =
                                          let uu____5567 =
                                            let uu____5568 =
                                              let uu____5579 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5579)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5568
                                             in
                                          (uu____5567,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5559
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5602 =
                                        let uu____5603 =
                                          let uu____5606 =
                                            let uu____5609 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5609
                                             in
                                          FStar_List.append decls' uu____5606
                                           in
                                        FStar_List.append decls uu____5603
                                         in
                                      (t1, uu____5602)))))
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
                     let uu____5630 =
                       let uu____5638 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5638,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5630  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5651 =
                       let uu____5659 =
                         let uu____5660 =
                           let uu____5671 =
                             let uu____5672 =
                               let uu____5677 =
                                 let uu____5678 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5678
                                  in
                               (f_has_t, uu____5677)  in
                             FStar_SMTEncoding_Util.mkImp uu____5672  in
                           ([[f_has_t]], [fsym], uu____5671)  in
                         let uu____5704 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5704 uu____5660  in
                       (uu____5659, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5651  in
                   let uu____5721 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5721)))
       | FStar_Syntax_Syntax.Tm_refine uu____5724 ->
           let uu____5731 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5741 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5741 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5750;
                 FStar_Syntax_Syntax.vars = uu____5751;_} ->
                 let uu____5758 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5758 with
                  | (b,f1) ->
                      let uu____5785 =
                        let uu____5786 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5786  in
                      (uu____5785, f1))
             | uu____5803 -> failwith "impossible"  in
           (match uu____5731 with
            | (x,f) ->
                let uu____5821 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5821 with
                 | (base_t,decls) ->
                     let uu____5832 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5832 with
                      | (x1,xtm,env') ->
                          let uu____5849 = encode_formula f env'  in
                          (match uu____5849 with
                           | (refinement,decls') ->
                               let uu____5860 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5860 with
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
                                      let uu____5888 =
                                        let uu____5899 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5910 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5899
                                          uu____5910
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5888
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5964 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5964 <> x1) &&
                                                (let uu____5968 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5968 <> fsym)))
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
                                    ((let uu____6001 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____6001
                                      then
                                        let uu____6005 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____6007 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6005 tkey_hash uu____6007
                                      else ());
                                     (let tsym =
                                        let uu____6014 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____6014
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
                                        let uu____6034 =
                                          let uu____6042 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____6042)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6034
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
                                        let uu____6062 =
                                          let uu____6070 =
                                            let uu____6071 =
                                              let uu____6082 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6082)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6071
                                             in
                                          (uu____6070,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6062
                                         in
                                      let t_kinding =
                                        let uu____6096 =
                                          let uu____6104 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6104,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6096
                                         in
                                      let t_interp =
                                        let uu____6118 =
                                          let uu____6126 =
                                            let uu____6127 =
                                              let uu____6138 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6138)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6127
                                             in
                                          (uu____6126,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6118
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1]  in
                                      let uu____6170 =
                                        let uu____6171 =
                                          let uu____6174 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6174
                                           in
                                        FStar_List.append decls uu____6171
                                         in
                                      (t1, uu____6170))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6178) ->
           let ttm =
             let uu____6196 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6196  in
           let uu____6198 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6198 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6210 =
                    let uu____6218 =
                      let uu____6220 =
                        let uu____6222 =
                          let uu____6224 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6224  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6222  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6220
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6218)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6210  in
                let uu____6230 =
                  let uu____6231 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6231  in
                (ttm, uu____6230))
       | FStar_Syntax_Syntax.Tm_app uu____6238 ->
           let uu____6255 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6255 with
            | (head1,args_e) ->
                let uu____6302 =
                  let uu____6317 =
                    let uu____6318 = FStar_Syntax_Subst.compress head1  in
                    uu____6318.FStar_Syntax_Syntax.n  in
                  (uu____6317, args_e)  in
                (match uu____6302 with
                 | uu____6335 when head_redex env head1 ->
                     let uu____6350 = whnf env t  in
                     encode_term uu____6350 env
                 | uu____6351 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6374 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6392) when
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
                       FStar_Syntax_Syntax.pos = uu____6414;
                       FStar_Syntax_Syntax.vars = uu____6415;_},uu____6416),uu____6417)
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
                       FStar_Syntax_Syntax.pos = uu____6443;
                       FStar_Syntax_Syntax.vars = uu____6444;_},uu____6445),
                    (v0,uu____6447)::(v1,uu____6449)::(v2,uu____6451)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6522 = encode_term v0 env  in
                     (match uu____6522 with
                      | (v01,decls0) ->
                          let uu____6533 = encode_term v1 env  in
                          (match uu____6533 with
                           | (v11,decls1) ->
                               let uu____6544 = encode_term v2 env  in
                               (match uu____6544 with
                                | (v21,decls2) ->
                                    let uu____6555 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6555,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6558)::(v1,uu____6560)::(v2,uu____6562)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6629 = encode_term v0 env  in
                     (match uu____6629 with
                      | (v01,decls0) ->
                          let uu____6640 = encode_term v1 env  in
                          (match uu____6640 with
                           | (v11,decls1) ->
                               let uu____6651 = encode_term v2 env  in
                               (match uu____6651 with
                                | (v21,decls2) ->
                                    let uu____6662 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6662,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6664)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6700)::(rng,uu____6702)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6753) ->
                     let e0 =
                       let uu____6775 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6775
                        in
                     ((let uu____6785 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6785
                       then
                         let uu____6790 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6790
                       else ());
                      (let e =
                         let uu____6798 =
                           let uu____6803 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6804 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6803
                             uu____6804
                            in
                         uu____6798 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6813),(arg,uu____6815)::[]) -> encode_term arg env
                 | uu____6850 ->
                     let uu____6865 = encode_args args_e env  in
                     (match uu____6865 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6934 = encode_term head1 env  in
                            match uu____6934 with
                            | (smt_head,decls') ->
                                let app_tm = mk_Apply_args smt_head args  in
                                (match ht_opt with
                                 | uu____6954 ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some
                                     (head_type,formals,c) ->
                                     ((let uu____7023 =
                                         FStar_TypeChecker_Env.debug
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (FStar_Options.Other "PartialApp")
                                          in
                                       if uu____7023
                                       then
                                         let uu____7027 =
                                           FStar_Syntax_Print.term_to_string
                                             head1
                                            in
                                         let uu____7029 =
                                           FStar_Syntax_Print.term_to_string
                                             head_type
                                            in
                                         let uu____7031 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", " formals
                                            in
                                         let uu____7034 =
                                           FStar_Syntax_Print.comp_to_string
                                             c
                                            in
                                         let uu____7036 =
                                           FStar_Syntax_Print.args_to_string
                                             args_e
                                            in
                                         FStar_Util.print5
                                           "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                           uu____7027 uu____7029 uu____7031
                                           uu____7034 uu____7036
                                       else ());
                                      (let uu____7041 =
                                         FStar_Util.first_N
                                           (FStar_List.length args_e) formals
                                          in
                                       match uu____7041 with
                                       | (formals1,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____7139  ->
                                                  fun uu____7140  ->
                                                    match (uu____7139,
                                                            uu____7140)
                                                    with
                                                    | ((bv,uu____7170),
                                                       (a,uu____7172)) ->
                                                        FStar_Syntax_Syntax.NT
                                                          (bv, a)) formals1
                                               args_e
                                              in
                                           let ty =
                                             let uu____7204 =
                                               FStar_Syntax_Util.arrow rest c
                                                in
                                             FStar_All.pipe_right uu____7204
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           ((let uu____7208 =
                                               FStar_TypeChecker_Env.debug
                                                 env.FStar_SMTEncoding_Env.tcenv
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____7208
                                             then
                                               let uu____7212 =
                                                 FStar_Syntax_Print.term_to_string
                                                   ty
                                                  in
                                               FStar_Util.print1
                                                 "Encoding partial application, after subst:\n\tty=%s\n"
                                                 uu____7212
                                             else ());
                                            (let uu____7217 =
                                               let uu____7230 =
                                                 FStar_List.fold_left2
                                                   (fun uu____7265  ->
                                                      fun uu____7266  ->
                                                        fun e  ->
                                                          match (uu____7265,
                                                                  uu____7266)
                                                          with
                                                          | ((t_hyps,decls1),
                                                             (bv,uu____7307))
                                                              ->
                                                              let t1 =
                                                                FStar_Syntax_Subst.subst
                                                                  subst1
                                                                  bv.FStar_Syntax_Syntax.sort
                                                                 in
                                                              let uu____7335
                                                                =
                                                                encode_term_pred
                                                                  FStar_Pervasives_Native.None
                                                                  t1 env e
                                                                 in
                                                              (match uu____7335
                                                               with
                                                               | (t_hyp,decls'1)
                                                                   ->
                                                                   ((
                                                                    let uu____7351
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7351
                                                                    then
                                                                    let uu____7355
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____7357
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7355
                                                                    uu____7357
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                   ([], []) formals1 args
                                                  in
                                               match uu____7230 with
                                               | (t_hyps,decls1) ->
                                                   let uu____7392 =
                                                     match smt_head.FStar_SMTEncoding_Term.tm
                                                     with
                                                     | FStar_SMTEncoding_Term.FreeV
                                                         uu____7401 ->
                                                         encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           head_type env
                                                           smt_head
                                                     | uu____7410 ->
                                                         (FStar_SMTEncoding_Util.mkTrue,
                                                           [])
                                                      in
                                                   (match uu____7392 with
                                                    | (t_head_hyp,decls'1) ->
                                                        let hyp =
                                                          FStar_SMTEncoding_Term.mk_and_l
                                                            (t_head_hyp ::
                                                            t_hyps)
                                                            FStar_Range.dummyRange
                                                           in
                                                        let uu____7426 =
                                                          encode_term_pred
                                                            FStar_Pervasives_Native.None
                                                            ty env app_tm
                                                           in
                                                        (match uu____7426
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
                                                             let uu____7448 =
                                                               let uu____7455
                                                                 =
                                                                 FStar_SMTEncoding_Term.fvs_subset_of
                                                                   cvars
                                                                   app_tm_vars
                                                                  in
                                                               if uu____7455
                                                               then
                                                                 ([app_tm],
                                                                   app_tm_vars)
                                                               else
                                                                 (let uu____7468
                                                                    =
                                                                    let uu____7470
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7470
                                                                     in
                                                                  if
                                                                    uu____7468
                                                                  then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                  else
                                                                    (
                                                                    (
                                                                    let uu____7483
                                                                    =
                                                                    let uu____7489
                                                                    =
                                                                    let uu____7491
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7491
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7489)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7483);
                                                                    ([],
                                                                    cvars)))
                                                                in
                                                             (match uu____7448
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
                                             match uu____7217 with
                                             | (vars,pattern,has_type,decls'')
                                                 ->
                                                 ((let uu____7538 =
                                                     FStar_TypeChecker_Env.debug
                                                       env.FStar_SMTEncoding_Env.tcenv
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____7538
                                                   then
                                                     let uu____7542 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         has_type
                                                        in
                                                     FStar_Util.print1
                                                       "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                       uu____7542
                                                   else ());
                                                  (let tkey_hash =
                                                     FStar_SMTEncoding_Term.hash_of_term
                                                       app_tm
                                                      in
                                                   let e_typing =
                                                     let uu____7550 =
                                                       let uu____7558 =
                                                         FStar_SMTEncoding_Term.mkForall
                                                           t0.FStar_Syntax_Syntax.pos
                                                           ([pattern], vars,
                                                             has_type)
                                                          in
                                                       let uu____7567 =
                                                         let uu____7569 =
                                                           let uu____7571 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm
                                                              in
                                                           FStar_Util.digest_of_string
                                                             uu____7571
                                                            in
                                                         Prims.op_Hat
                                                           "partial_app_typing_"
                                                           uu____7569
                                                          in
                                                       (uu____7558,
                                                         (FStar_Pervasives_Native.Some
                                                            "Partial app typing"),
                                                         uu____7567)
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____7550
                                                      in
                                                   let uu____7577 =
                                                     let uu____7580 =
                                                       let uu____7583 =
                                                         let uu____7586 =
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
                                                           decls'' uu____7586
                                                          in
                                                       FStar_List.append
                                                         decls' uu____7583
                                                        in
                                                     FStar_List.append decls
                                                       uu____7580
                                                      in
                                                   (app_tm, uu____7577))))))))
                             in
                          let encode_full_app fv =
                            let uu____7606 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____7606 with
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
                                   FStar_Syntax_Syntax.pos = uu____7649;
                                   FStar_Syntax_Syntax.vars = uu____7650;_},uu____7651)
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
                                   FStar_Syntax_Syntax.pos = uu____7658;
                                   FStar_Syntax_Syntax.vars = uu____7659;_},uu____7660)
                                ->
                                let uu____7665 =
                                  let uu____7666 =
                                    let uu____7671 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7671
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7666
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7665
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7701 =
                                  let uu____7702 =
                                    let uu____7707 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7707
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7702
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7701
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7736,(FStar_Util.Inl t1,uu____7738),uu____7739)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7786,(FStar_Util.Inr c,uu____7788),uu____7789)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7836 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let uu____7860 =
                                 let head_type2 =
                                   let uu____7882 =
                                     FStar_TypeChecker_Normalize.normalize_refinement
                                       [FStar_TypeChecker_Env.Weak;
                                       FStar_TypeChecker_Env.HNF;
                                       FStar_TypeChecker_Env.EraseUniverses]
                                       env.FStar_SMTEncoding_Env.tcenv
                                       head_type1
                                      in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.unrefine uu____7882
                                    in
                                 let uu____7885 =
                                   curried_arrow_formals_comp head_type2  in
                                 match uu____7885 with
                                 | (formals,c) ->
                                     if
                                       (FStar_List.length formals) <
                                         (FStar_List.length args)
                                     then
                                       let head_type3 =
                                         let uu____7938 =
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
                                           uu____7938
                                          in
                                       let uu____7941 =
                                         curried_arrow_formals_comp
                                           head_type3
                                          in
                                       (match uu____7941 with
                                        | (formals1,c1) ->
                                            (head_type3, formals1, c1))
                                     else (head_type2, formals, c)
                                  in
                               (match uu____7860 with
                                | (head_type2,formals,c) ->
                                    ((let uu____8024 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "PartialApp")
                                         in
                                      if uu____8024
                                      then
                                        let uu____8028 =
                                          FStar_Syntax_Print.term_to_string
                                            head_type2
                                           in
                                        let uu____8030 =
                                          FStar_Syntax_Print.binders_to_string
                                            ", " formals
                                           in
                                        let uu____8033 =
                                          FStar_Syntax_Print.args_to_string
                                            args_e
                                           in
                                        FStar_Util.print3
                                          "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                          uu____8028 uu____8030 uu____8033
                                      else ());
                                     (match head2.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.pos =
                                               uu____8043;
                                             FStar_Syntax_Syntax.vars =
                                               uu____8044;_},uu____8045)
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
                                      | uu____8063 ->
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
           let uu____8152 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8152 with
            | (bs1,body1,opening) ->
                let fallback uu____8175 =
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
                  let uu____8185 =
                    let uu____8186 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8186
                     in
                  let uu____8188 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8185, uu____8188)  in
                let is_impure rc =
                  let uu____8198 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8198 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8213 =
                          let uu____8226 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8226
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8213 with
                         | (t1,uu____8229,uu____8230) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8248 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8248
                  then
                    let uu____8253 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8253
                  else
                    (let uu____8256 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8256
                     then
                       let uu____8261 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8261
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8269 =
                         let uu____8275 =
                           let uu____8277 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8277
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8275)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8269);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8282 =
                       (is_impure rc) &&
                         (let uu____8285 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8285)
                        in
                     if uu____8282
                     then fallback ()
                     else
                       (let uu____8294 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8294 with
                        | (vars,guards,envbody,decls,uu____8319) ->
                            let body2 =
                              let uu____8333 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8333
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____8338 = encode_term body2 envbody  in
                            (match uu____8338 with
                             | (body3,decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect
                                    in
                                 let uu____8351 =
                                   let uu____8360 = codomain_eff rc  in
                                   match uu____8360 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8379 = encode_term tfun env
                                          in
                                       (match uu____8379 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8351 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8413 =
                                          let uu____8424 =
                                            let uu____8425 =
                                              let uu____8430 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8430, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8425
                                             in
                                          ([], vars, uu____8424)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8413
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8438 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8454 =
                                              let uu____8457 =
                                                let uu____8468 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____8468
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8457
                                               in
                                            let uu____8495 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____8454, uu____8495)
                                         in
                                      (match uu____8438 with
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
                                           ((let uu____8518 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8518
                                             then
                                               let uu____8523 =
                                                 let uu____8525 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8525
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8535 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8523 uu____8535
                                             else ());
                                            (let uu____8540 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8540 with
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 ((let uu____8549 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8549
                                                   then
                                                     let uu____8554 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t1
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8554
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
                                                   let uu____8567 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8567
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8576 =
                                                     let uu____8584 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8584)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8576
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8598 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8606
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue))
                                                              in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8598
                                                             is_pure
                                                            in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8607 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax)
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym
                                                          in
                                                       let uu____8621 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                          in
                                                       [uu____8621]
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
                                                       let uu____8629 =
                                                         let uu____8630 =
                                                           let uu____8638 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8638,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8630
                                                          in
                                                       [uu____8629]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8653 =
                                                     let uu____8661 =
                                                       let uu____8662 =
                                                         let uu____8673 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8673)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8662
                                                        in
                                                     (uu____8661,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8653
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8687 =
                                                   let uu____8688 =
                                                     let uu____8691 =
                                                       let uu____8694 =
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
                                                         decls'' uu____8694
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8691
                                                      in
                                                   FStar_List.append decls
                                                     uu____8688
                                                    in
                                                 (f, uu____8687)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8697,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8698;
                          FStar_Syntax_Syntax.lbunivs = uu____8699;
                          FStar_Syntax_Syntax.lbtyp = uu____8700;
                          FStar_Syntax_Syntax.lbeff = uu____8701;
                          FStar_Syntax_Syntax.lbdef = uu____8702;
                          FStar_Syntax_Syntax.lbattrs = uu____8703;
                          FStar_Syntax_Syntax.lbpos = uu____8704;_}::uu____8705),uu____8706)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8740;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8742;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8744;
                FStar_Syntax_Syntax.lbpos = uu____8745;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8772,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                          FStar_Syntax_Syntax.lbunivs = uu____8774;
                          FStar_Syntax_Syntax.lbtyp = uu____8775;
                          FStar_Syntax_Syntax.lbeff = uu____8776;
                          FStar_Syntax_Syntax.lbdef = uu____8777;
                          FStar_Syntax_Syntax.lbattrs = uu____8778;
                          FStar_Syntax_Syntax.lbpos = uu____8779;_}::[]),uu____8780)
           ->
           let uu____8806 =
             let uu____8807 =
               let uu____8813 =
                 FStar_Ident.text_of_id x.FStar_Syntax_Syntax.ppname  in
               let uu____8815 = FStar_Syntax_Syntax.range_of_bv x  in
               (uu____8813, uu____8815)  in
             FStar_SMTEncoding_Env.Inner_let_rec uu____8807  in
           FStar_Exn.raise uu____8806
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
              let uu____8873 =
                let uu____8878 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8878 env  in
              match uu____8873 with
              | (ee1,decls1) ->
                  let uu____8903 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8903 with
                   | (xs,e21) ->
                       let uu____8928 = FStar_List.hd xs  in
                       (match uu____8928 with
                        | (x1,uu____8946) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____8952 = encode_body e21 env'  in
                            (match uu____8952 with
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
            let uu____8982 =
              let uu____8990 =
                let uu____8991 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8991  in
              FStar_SMTEncoding_Env.gen_term_var env uu____8990  in
            match uu____8982 with
            | (scrsym,scr',env1) ->
                let uu____9001 = encode_term e env1  in
                (match uu____9001 with
                 | (scr,decls) ->
                     let uu____9012 =
                       let encode_branch b uu____9041 =
                         match uu____9041 with
                         | (else_case,decls1) ->
                             let uu____9060 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9060 with
                              | (p,w,br) ->
                                  let uu____9086 = encode_pat env1 p  in
                                  (match uu____9086 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9123  ->
                                                   match uu____9123 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9130 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9152 =
                                               encode_term w1 env2  in
                                             (match uu____9152 with
                                              | (w2,decls2) ->
                                                  let uu____9165 =
                                                    let uu____9166 =
                                                      let uu____9171 =
                                                        let uu____9172 =
                                                          let uu____9177 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9177)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9172
                                                         in
                                                      (guard, uu____9171)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9166
                                                     in
                                                  (uu____9165, decls2))
                                          in
                                       (match uu____9130 with
                                        | (guard1,decls2) ->
                                            let uu____9192 =
                                              encode_br br env2  in
                                            (match uu____9192 with
                                             | (br1,decls3) ->
                                                 let uu____9205 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9205,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9012 with
                      | (match_tm,decls1) ->
                          let uu____9226 =
                            let uu____9227 =
                              let uu____9238 =
                                let uu____9245 =
                                  let uu____9250 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9250, scr)  in
                                [uu____9245]  in
                              (uu____9238, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9227
                              FStar_Range.dummyRange
                             in
                          (uu____9226, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9273 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9273
       then
         let uu____9276 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9276
       else ());
      (let uu____9281 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9281 with
       | (vars,pat_term) ->
           let uu____9298 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9340  ->
                     fun v1  ->
                       match uu____9340 with
                       | (env1,vars1) ->
                           let uu____9376 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____9376 with
                            | (xx,uu____9395,env2) ->
                                let uu____9399 =
                                  let uu____9406 =
                                    let uu____9411 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____9411)  in
                                  uu____9406 :: vars1  in
                                (env2, uu____9399))) (env, []))
              in
           (match uu____9298 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9466 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9467 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9468 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9476 = encode_const c env1  in
                      (match uu____9476 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9484::uu____9485 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9489 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9512 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9512 with
                        | (uu____9520,uu____9521::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9526 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9562  ->
                                  match uu____9562 with
                                  | (arg,uu____9572) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9581 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9581))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9613) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9644 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9669 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9715  ->
                                  match uu____9715 with
                                  | (arg,uu____9731) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9740 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9740))
                         in
                      FStar_All.pipe_right uu____9669 FStar_List.flatten
                   in
                let pat_term1 uu____9771 = encode_term pat_term env1  in
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
      let uu____9781 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9829  ->
                fun uu____9830  ->
                  match (uu____9829, uu____9830) with
                  | ((tms,decls),(t,uu____9870)) ->
                      let uu____9897 = encode_term t env  in
                      (match uu____9897 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9781 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____9975  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1371_9984 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1371_9984.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1371_9984.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1371_9984.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1371_9984.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1371_9984.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1371_9984.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1371_9984.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1371_9984.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1371_9984.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1371_9984.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1376_10001 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1376_10001.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1376_10001.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1376_10001.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1376_10001.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1376_10001.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1376_10001.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1376_10001.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1376_10001.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1376_10001.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1376_10001.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____10017 = FStar_Syntax_Util.head_and_args t  in
        match uu____10017 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10080::(x,uu____10082)::(t1,uu____10084)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10151 = encode_term x env1  in
                 (match uu____10151 with
                  | (x1,decls) ->
                      let uu____10162 = encode_term t1 env1  in
                      (match uu____10162 with
                       | (t2,decls') ->
                           let uu____10173 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10173, (FStar_List.append decls decls'))))
             | uu____10174 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10217  ->
             match uu____10217 with
             | (pats_l1,decls) ->
                 let uu____10262 =
                   FStar_List.fold_right
                     (fun uu____10297  ->
                        fun uu____10298  ->
                          match (uu____10297, uu____10298) with
                          | ((p,uu____10340),(pats1,decls1)) ->
                              let uu____10375 = encode_smt_pattern p  in
                              (match uu____10375 with
                               | (t,d) ->
                                   let uu____10390 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10390 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10407 =
                                            let uu____10413 =
                                              let uu____10415 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10417 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10415 uu____10417
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10413)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10407);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10262 with
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
        let uu____10477 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10477
        then
          let uu____10482 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10484 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10482 uu____10484
        else ()  in
      let enc f r l =
        let uu____10526 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10558 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10558 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10526 with
        | (decls,args) ->
            let uu____10589 =
              let uu___1440_10590 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1440_10590.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1440_10590.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10589, decls)
         in
      let const_op f r uu____10625 =
        let uu____10638 = f r  in (uu____10638, [])  in
      let un_op f l =
        let uu____10661 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10661  in
      let bin_op f uu___2_10681 =
        match uu___2_10681 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10692 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10733 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10758  ->
                 match uu____10758 with
                 | (t,uu____10774) ->
                     let uu____10779 = encode_formula t env  in
                     (match uu____10779 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10733 with
        | (decls,phis) ->
            let uu____10808 =
              let uu___1470_10809 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1470_10809.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1470_10809.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10808, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10872  ->
               match uu____10872 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10893) -> false
                    | uu____10896 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10915 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10915
        else
          (let uu____10932 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10932 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11000 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11032 =
                       let uu____11037 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11038 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11037, uu____11038)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11032
                 | uu____11039 -> failwith "Impossible")
             in
          uu____11000 r args
        else
          (let uu____11045 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11045)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11107 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11139 =
                       let uu____11144 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11145 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11144, uu____11145)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11139
                 | uu____11146 -> failwith "Impossible")
             in
          uu____11107 r args
        else
          (let uu____11152 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11152)
         in
      let mk_imp1 r uu___3_11181 =
        match uu___3_11181 with
        | (lhs,uu____11187)::(rhs,uu____11189)::[] ->
            let uu____11230 = encode_formula rhs env  in
            (match uu____11230 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11245) ->
                      (l1, decls1)
                  | uu____11250 ->
                      let uu____11251 = encode_formula lhs env  in
                      (match uu____11251 with
                       | (l2,decls2) ->
                           let uu____11262 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11262, (FStar_List.append decls1 decls2)))))
        | uu____11263 -> failwith "impossible"  in
      let mk_ite r uu___4_11291 =
        match uu___4_11291 with
        | (guard,uu____11297)::(_then,uu____11299)::(_else,uu____11301)::[]
            ->
            let uu____11358 = encode_formula guard env  in
            (match uu____11358 with
             | (g,decls1) ->
                 let uu____11369 = encode_formula _then env  in
                 (match uu____11369 with
                  | (t,decls2) ->
                      let uu____11380 = encode_formula _else env  in
                      (match uu____11380 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11392 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11422 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11422  in
      let connectives =
        let uu____11452 =
          let uu____11477 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11477)  in
        let uu____11520 =
          let uu____11547 =
            let uu____11572 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11572)  in
          let uu____11615 =
            let uu____11642 =
              let uu____11669 =
                let uu____11694 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11694)  in
              let uu____11737 =
                let uu____11764 =
                  let uu____11791 =
                    let uu____11816 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11816)  in
                  [uu____11791;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11764  in
              uu____11669 :: uu____11737  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11642  in
          uu____11547 :: uu____11615  in
        uu____11452 :: uu____11520  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12361 = encode_formula phi' env  in
            (match uu____12361 with
             | (phi2,decls) ->
                 let uu____12372 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12372, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12374 ->
            let uu____12381 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12381 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12420 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12420 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12432;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12434;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12436;
                 FStar_Syntax_Syntax.lbpos = uu____12437;_}::[]),e2)
            ->
            let uu____12464 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12464 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12517::(x,uu____12519)::(t,uu____12521)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12588 = encode_term x env  in
                 (match uu____12588 with
                  | (x1,decls) ->
                      let uu____12599 = encode_term t env  in
                      (match uu____12599 with
                       | (t1,decls') ->
                           let uu____12610 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12610, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12613)::(msg,uu____12615)::(phi2,uu____12617)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12684 =
                   let uu____12689 =
                     let uu____12690 = FStar_Syntax_Subst.compress r  in
                     uu____12690.FStar_Syntax_Syntax.n  in
                   let uu____12693 =
                     let uu____12694 = FStar_Syntax_Subst.compress msg  in
                     uu____12694.FStar_Syntax_Syntax.n  in
                   (uu____12689, uu____12693)  in
                 (match uu____12684 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12703))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12714 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12721)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12756 when head_redex env head2 ->
                 let uu____12771 = whnf env phi1  in
                 encode_formula uu____12771 env
             | uu____12772 ->
                 let uu____12787 = encode_term phi1 env  in
                 (match uu____12787 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12799 =
                          let uu____12801 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12802 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12801 uu____12802
                           in
                        if uu____12799
                        then tt
                        else
                          (let uu___1657_12806 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___1657_12806.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___1657_12806.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12807 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12807, decls)))
        | uu____12808 ->
            let uu____12809 = encode_term phi1 env  in
            (match uu____12809 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12821 =
                     let uu____12823 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12824 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12823 uu____12824  in
                   if uu____12821
                   then tt
                   else
                     (let uu___1665_12828 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1665_12828.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1665_12828.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12829 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12829, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12873 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12873 with
        | (vars,guards,env2,decls,uu____12912) ->
            let uu____12925 = encode_smt_patterns ps env2  in
            (match uu____12925 with
             | (pats,decls') ->
                 let uu____12962 = encode_formula body env2  in
                 (match uu____12962 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12994;
                             FStar_SMTEncoding_Term.rng = uu____12995;_}::[])::[]
                            when
                            let uu____13015 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13015 = gf -> []
                        | uu____13018 -> guards  in
                      let uu____13023 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13023, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13034 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13034 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13043 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13149  ->
                     match uu____13149 with
                     | (l,uu____13174) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13043 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13243,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13335 = encode_q_body env vars pats body  in
             match uu____13335 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13380 =
                     let uu____13391 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13391)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13380
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13422 = encode_q_body env vars pats body  in
             match uu____13422 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13466 =
                   let uu____13467 =
                     let uu____13478 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13478)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13467
                    in
                 (uu____13466, decls))))
