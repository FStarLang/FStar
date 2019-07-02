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
              | uu____946 -> failwith "impossible: isTotFun_axioms"  in
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
                  (let uu____1017 = FStar_Util.first_N arity args  in
                   match uu____1017 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1041 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____1041 arity n_args rng)
  
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
          let uu____1064 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____1064 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1073  ->
    match uu___1_1073 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1079 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1127;
                       FStar_SMTEncoding_Term.rng = uu____1128;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1159) ->
              let uu____1169 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1186 -> false) args (FStar_List.rev xs))
                 in
              if uu____1169
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f  in
                ((let uu____1195 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp")
                     in
                  if uu____1195
                  then
                    let uu____1200 = FStar_SMTEncoding_Term.print_smt_term t
                       in
                    let uu____1202 =
                      match n1 with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x
                       in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1200 uu____1202
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1212,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1216 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1224 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1224))
                 in
              if uu____1216
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1231 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____1249 'Auu____1250 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1249) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1250) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1308  ->
                  match uu____1308 with
                  | (x,uu____1314) ->
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
              let uu____1322 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1334 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1334) uu____1322 tl1
               in
            let uu____1337 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1364  ->
                      match uu____1364 with
                      | (b,uu____1371) ->
                          let uu____1372 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1372))
               in
            (match uu____1337 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1379) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____1393 =
                   let uu____1399 =
                     let uu____1401 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1401
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1399)  in
                 FStar_Errors.log_issue pos uu____1393)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1687 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1702 ->
            let uu____1709 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1709
        | uu____1711 ->
            if norm1
            then let uu____1713 = whnf env t1  in aux false uu____1713
            else
              (let uu____1717 =
                 let uu____1719 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1721 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1719 uu____1721
                  in
               failwith uu____1717)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1763) ->
        let uu____1768 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1768 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1789 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1789)
              | uu____1796 -> (args, res)))
    | uu____1797 ->
        let uu____1798 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1798)
  
let is_arithmetic_primitive :
  'Auu____1812 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1812 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1835::uu____1836::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1840::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1843 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1874 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1897 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1907 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1907)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1949)::uu____1950::uu____1951::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____2002)::uu____2003::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2040 -> false
  
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
          let uu____2364 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2364, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2366 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2366, [])
      | FStar_Const.Const_char c1 ->
          let uu____2369 =
            let uu____2370 =
              let uu____2378 =
                let uu____2381 =
                  let uu____2382 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2382  in
                [uu____2381]  in
              ("FStar.Char.__char_of_int", uu____2378)  in
            FStar_SMTEncoding_Util.mkApp uu____2370  in
          (uu____2369, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2400 =
            let uu____2401 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2401  in
          (uu____2400, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2422) ->
          let uu____2425 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2425, [])
      | FStar_Const.Const_range uu____2426 ->
          let uu____2427 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2427, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2430 =
            let uu____2431 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2431  in
          (uu____2430, [])
      | c1 ->
          let uu____2433 =
            let uu____2435 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2435  in
          failwith uu____2433

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
        (let uu____2464 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2464
         then
           let uu____2467 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2467
         else ());
        (let uu____2473 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2555  ->
                   fun b  ->
                     match uu____2555 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2620 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2636 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2636 with
                           | (xxsym,xx,env') ->
                               let uu____2661 =
                                 let uu____2666 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2666 env1 xx
                                  in
                               (match uu____2661 with
                                | (guard_x_t,decls') ->
                                    let uu____2681 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2681, guard_x_t, env', decls', x))
                            in
                         (match uu____2620 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2473 with
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
          let uu____2781 = encode_term t env  in
          match uu____2781 with
          | (t1,decls) ->
              let uu____2792 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2792, decls)

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
          let uu____2803 = encode_term t env  in
          match uu____2803 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2818 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2818, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2820 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2820, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2826 = encode_args args_e env  in
        match uu____2826 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2845 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2867 = FStar_List.hd arg_tms1  in unbox uu____2867
               in
            let binary unbox arg_tms1 =
              let uu____2892 =
                let uu____2893 = FStar_List.hd arg_tms1  in unbox uu____2893
                 in
              let uu____2894 =
                let uu____2895 =
                  let uu____2896 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2896  in
                unbox uu____2895  in
              (uu____2892, uu____2894)  in
            let mk_default uu____2904 =
              let uu____2905 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2905 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2994 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2994
              then
                let uu____2997 =
                  let uu____2998 = mk_args ts  in op uu____2998  in
                FStar_All.pipe_right uu____2997 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____3056 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3056
              then
                let uu____3059 = binary unbox ts  in
                match uu____3059 with
                | (t1,t2) ->
                    let uu____3066 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3066 box
              else
                (let uu____3072 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3072
                 then
                   let uu____3075 =
                     let uu____3076 = binary unbox ts  in op uu____3076  in
                   FStar_All.pipe_right uu____3075 box
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
            let uu____3511 =
              let uu____3521 =
                FStar_List.tryFind
                  (fun uu____3545  ->
                     match uu____3545 with
                     | (l,uu____3556) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3521 FStar_Util.must  in
            (match uu____3511 with
             | (uu____3600,op) ->
                 let uu____3612 = op arg_tms  in (uu____3612, decls))

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
        let uu____3628 = FStar_List.hd args_e  in
        match uu____3628 with
        | (tm_sz,uu____3644) ->
            let uu____3653 = uu____3628  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3664 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3690::(sz_arg,uu____3692)::uu____3693::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3760 =
                    let uu____3761 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3761  in
                  let uu____3788 =
                    let uu____3792 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3792  in
                  (uu____3760, uu____3788)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3799::(sz_arg,uu____3801)::uu____3802::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3869 =
                    let uu____3871 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3871
                     in
                  failwith uu____3869
              | uu____3881 ->
                  let uu____3896 = FStar_List.tail args_e  in
                  (uu____3896, FStar_Pervasives_Native.None)
               in
            (match uu____3664 with
             | (arg_tms,ext_sz) ->
                 let uu____3923 = encode_args arg_tms env  in
                 (match uu____3923 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3944 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3956 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3956  in
                      let unary_arith arg_tms2 =
                        let uu____3967 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3967  in
                      let binary arg_tms2 =
                        let uu____3982 =
                          let uu____3983 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3983
                           in
                        let uu____3984 =
                          let uu____3985 =
                            let uu____3986 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3986  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3985
                           in
                        (uu____3982, uu____3984)  in
                      let binary_arith arg_tms2 =
                        let uu____4003 =
                          let uu____4004 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4004
                           in
                        let uu____4005 =
                          let uu____4006 =
                            let uu____4007 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4007  in
                          FStar_SMTEncoding_Term.unboxInt uu____4006  in
                        (uu____4003, uu____4005)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____4065 =
                          let uu____4066 = mk_args ts  in op uu____4066  in
                        FStar_All.pipe_right uu____4065 resBox  in
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
                        let uu____4198 =
                          let uu____4203 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4203  in
                        let uu____4212 =
                          let uu____4217 =
                            let uu____4219 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4219  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4217  in
                        mk_bv uu____4198 unary uu____4212 arg_tms2  in
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
                      let uu____4459 =
                        let uu____4469 =
                          FStar_List.tryFind
                            (fun uu____4493  ->
                               match uu____4493 with
                               | (l,uu____4504) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4469 FStar_Util.must  in
                      (match uu____4459 with
                       | (uu____4550,op) ->
                           let uu____4562 = op arg_tms1  in
                           (uu____4562, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___587_4572 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___587_4572.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___587_4572.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___587_4572.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___587_4572.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___587_4572.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___587_4572.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___587_4572.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___587_4572.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___587_4572.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___587_4572.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4574 = encode_term t env1  in
      match uu____4574 with
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
               (uu____4600,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4601;
                             FStar_SMTEncoding_Term.freevars = uu____4602;
                             FStar_SMTEncoding_Term.rng = uu____4603;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4604;
                  FStar_SMTEncoding_Term.freevars = uu____4605;
                  FStar_SMTEncoding_Term.rng = uu____4606;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4652 ->
               let uu____4653 = encode_formula t env1  in
               (match uu____4653 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4673 =
                            let uu____4678 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4678, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4673
                      | uu____4679 ->
                          let uu____4680 =
                            let uu____4691 =
                              let uu____4692 =
                                let uu____4697 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4697, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4692  in
                            ([[valid_tm]], vars, uu____4691)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4680
                       in
                    let ax =
                      let uu____4707 =
                        let uu____4715 =
                          let uu____4717 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4717  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4715)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4707  in
                    let uu____4723 =
                      let uu____4724 =
                        let uu____4727 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4727  in
                      FStar_List.append decls uu____4724  in
                    (tm, uu____4723)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4739 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4739
       then
         let uu____4744 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4746 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4748 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4744 uu____4746
           uu____4748
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4757 ->
           let uu____4780 =
             let uu____4782 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4785 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4787 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4789 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4782
               uu____4785 uu____4787 uu____4789
              in
           failwith uu____4780
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4796 =
             let uu____4798 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4801 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4803 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4805 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4798
               uu____4801 uu____4803 uu____4805
              in
           failwith uu____4796
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4815 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4815
             then
               let uu____4820 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4822 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4820
                 uu____4822
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4828 =
             let uu____4830 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4830
              in
           failwith uu____4828
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4839),uu____4840) ->
           let uu____4889 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4899 -> false  in
           if uu____4889
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4917) ->
           let tv =
             let uu____4923 =
               let uu____4930 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4930
                in
             uu____4923 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4934 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4934
             then
               let uu____4939 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4941 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4939
                 uu____4941
             else ());
            (let t1 =
               let uu____4949 =
                 let uu____4960 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4960]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4949
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4986) ->
           encode_term t1
             (let uu___659_5012 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___659_5012.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___659_5012.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___659_5012.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___659_5012.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___659_5012.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___659_5012.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___659_5012.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___659_5012.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___659_5012.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___659_5012.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5015) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5023 = head_redex env t  in
           if uu____5023
           then let uu____5030 = whnf env t  in encode_term uu____5030 env
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
              let uu____5037 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____5061 ->
                      let sym_name =
                        let uu____5072 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____5072  in
                      let uu____5075 =
                        let uu____5078 =
                          let uu____5079 =
                            let uu____5087 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____5087,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____5079  in
                        [uu____5078]  in
                      (uu____5075, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____5094,[]) ->
                      let sym_name =
                        let uu____5099 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____5099  in
                      let uu____5102 =
                        let uu____5105 =
                          let uu____5106 =
                            let uu____5114 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____5114,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____5106  in
                        [uu____5105]  in
                      (uu____5102, sym_name)
                  | uu____5121 -> ([], "")
                else ([], "")  in
              match uu____5037 with
              | (aux_decls,sym_name) ->
                  let uu____5144 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____5144))
       | FStar_Syntax_Syntax.Tm_type uu____5152 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5154) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5184 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5184 with
            | (binders1,res) ->
                let uu____5195 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5195
                then
                  let uu____5202 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5202 with
                   | (vars,guards_l,env',decls,uu____5227) ->
                       let fsym =
                         let uu____5241 =
                           let uu____5247 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5247, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5241  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5253 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___713_5262 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___713_5262.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___713_5262.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___713_5262.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___713_5262.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___713_5262.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___713_5262.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___713_5262.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___713_5262.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___713_5262.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___713_5262.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___713_5262.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___713_5262.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___713_5262.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___713_5262.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___713_5262.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___713_5262.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___713_5262.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___713_5262.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___713_5262.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___713_5262.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___713_5262.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___713_5262.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___713_5262.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___713_5262.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___713_5262.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___713_5262.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___713_5262.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___713_5262.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___713_5262.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___713_5262.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___713_5262.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___713_5262.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___713_5262.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___713_5262.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___713_5262.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___713_5262.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___713_5262.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___713_5262.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___713_5262.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___713_5262.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___713_5262.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___713_5262.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____5253 with
                        | (pre_opt,res_t) ->
                            let uu____5274 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5274 with
                             | (res_pred,decls') ->
                                 let uu____5285 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5298 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5298, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5302 =
                                         encode_formula pre env'  in
                                       (match uu____5302 with
                                        | (guard,decls0) ->
                                            let uu____5315 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5315, decls0))
                                    in
                                 (match uu____5285 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        let uu____5330 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv)
                                           in
                                        FStar_All.pipe_right uu____5330
                                          FStar_Syntax_Util.is_pure_comp
                                         in
                                      let t_interp =
                                        let uu____5339 =
                                          let uu____5350 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5350)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____5339
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
                                        let uu____5372 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5372
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5391 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5393 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5391 <> uu____5393))
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
                                        let uu____5421 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix1 uu____5421  in
                                      let tsym =
                                        let uu____5425 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix1 uu____5425  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5439 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5439
                                        then
                                          let uu____5442 =
                                            let uu____5444 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5444 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5442
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____5457 =
                                          let uu____5465 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5465)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5457
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5484 =
                                          let uu____5492 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5492,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5484
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
                                        let uu____5509 =
                                          let uu____5517 =
                                            let uu____5518 =
                                              let uu____5529 =
                                                let uu____5530 =
                                                  let uu____5535 =
                                                    let uu____5536 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5536
                                                     in
                                                  (f_has_t, uu____5535)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5530
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5529)
                                               in
                                            let uu____5554 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5554 uu____5518  in
                                          (uu____5517,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5509
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5577 =
                                          let uu____5585 =
                                            let uu____5586 =
                                              let uu____5597 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5597)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5586
                                             in
                                          (uu____5585,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5577
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5620 =
                                        let uu____5621 =
                                          let uu____5624 =
                                            let uu____5627 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5627
                                             in
                                          FStar_List.append decls' uu____5624
                                           in
                                        FStar_List.append decls uu____5621
                                         in
                                      (t1, uu____5620)))))
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
                     let uu____5648 =
                       let uu____5656 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5656,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5648  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5669 =
                       let uu____5677 =
                         let uu____5678 =
                           let uu____5689 =
                             let uu____5690 =
                               let uu____5695 =
                                 let uu____5696 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5696
                                  in
                               (f_has_t, uu____5695)  in
                             FStar_SMTEncoding_Util.mkImp uu____5690  in
                           ([[f_has_t]], [fsym], uu____5689)  in
                         let uu____5722 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5722 uu____5678  in
                       (uu____5677, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5669  in
                   let uu____5739 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5739)))
       | FStar_Syntax_Syntax.Tm_refine uu____5742 ->
           let uu____5749 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5759 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5759 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5768;
                 FStar_Syntax_Syntax.vars = uu____5769;_} ->
                 let uu____5776 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5776 with
                  | (b,f1) ->
                      let uu____5803 =
                        let uu____5804 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5804  in
                      (uu____5803, f1))
             | uu____5821 -> failwith "impossible"  in
           (match uu____5749 with
            | (x,f) ->
                let uu____5839 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5839 with
                 | (base_t,decls) ->
                     let uu____5850 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5850 with
                      | (x1,xtm,env') ->
                          let uu____5867 = encode_formula f env'  in
                          (match uu____5867 with
                           | (refinement,decls') ->
                               let uu____5878 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5878 with
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
                                      let uu____5906 =
                                        let uu____5917 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5928 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5917
                                          uu____5928
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5906
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5982 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5982 <> x1) &&
                                                (let uu____5986 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5986 <> fsym)))
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
                                    ((let uu____6019 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____6019
                                      then
                                        let uu____6023 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____6025 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6023 tkey_hash uu____6025
                                      else ());
                                     (let tsym =
                                        let uu____6032 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____6032
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
                                        let uu____6052 =
                                          let uu____6060 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____6060)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6052
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
                                        let uu____6080 =
                                          let uu____6088 =
                                            let uu____6089 =
                                              let uu____6100 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6100)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6089
                                             in
                                          (uu____6088,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6080
                                         in
                                      let t_kinding =
                                        let uu____6114 =
                                          let uu____6122 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6122,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6114
                                         in
                                      let t_interp =
                                        let uu____6136 =
                                          let uu____6144 =
                                            let uu____6145 =
                                              let uu____6156 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6156)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6145
                                             in
                                          (uu____6144,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6136
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1]  in
                                      let uu____6188 =
                                        let uu____6189 =
                                          let uu____6192 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6192
                                           in
                                        FStar_List.append decls uu____6189
                                         in
                                      (t1, uu____6188))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6196) ->
           let ttm =
             let uu____6214 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6214  in
           let uu____6216 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6216 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6228 =
                    let uu____6236 =
                      let uu____6238 =
                        let uu____6240 =
                          let uu____6242 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6242  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6240  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6238
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6236)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6228  in
                let uu____6248 =
                  let uu____6249 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6249  in
                (ttm, uu____6248))
       | FStar_Syntax_Syntax.Tm_app uu____6256 ->
           let uu____6273 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6273 with
            | (head1,args_e) ->
                let uu____6320 =
                  let uu____6335 =
                    let uu____6336 = FStar_Syntax_Subst.compress head1  in
                    uu____6336.FStar_Syntax_Syntax.n  in
                  (uu____6335, args_e)  in
                (match uu____6320 with
                 | uu____6353 when head_redex env head1 ->
                     let uu____6368 = whnf env t  in
                     encode_term uu____6368 env
                 | uu____6369 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6392 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6410) when
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
                       FStar_Syntax_Syntax.pos = uu____6432;
                       FStar_Syntax_Syntax.vars = uu____6433;_},uu____6434),uu____6435)
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
                       FStar_Syntax_Syntax.pos = uu____6461;
                       FStar_Syntax_Syntax.vars = uu____6462;_},uu____6463),
                    (v0,uu____6465)::(v1,uu____6467)::(v2,uu____6469)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6540 = encode_term v0 env  in
                     (match uu____6540 with
                      | (v01,decls0) ->
                          let uu____6551 = encode_term v1 env  in
                          (match uu____6551 with
                           | (v11,decls1) ->
                               let uu____6562 = encode_term v2 env  in
                               (match uu____6562 with
                                | (v21,decls2) ->
                                    let uu____6573 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6573,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6576)::(v1,uu____6578)::(v2,uu____6580)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6647 = encode_term v0 env  in
                     (match uu____6647 with
                      | (v01,decls0) ->
                          let uu____6658 = encode_term v1 env  in
                          (match uu____6658 with
                           | (v11,decls1) ->
                               let uu____6669 = encode_term v2 env  in
                               (match uu____6669 with
                                | (v21,decls2) ->
                                    let uu____6680 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6680,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6682)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6718)::(rng,uu____6720)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6771) ->
                     let e0 =
                       let uu____6793 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6793
                        in
                     ((let uu____6803 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6803
                       then
                         let uu____6808 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6808
                       else ());
                      (let e =
                         let uu____6816 =
                           let uu____6821 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6822 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6821
                             uu____6822
                            in
                         uu____6816 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6831),(arg,uu____6833)::[]) -> encode_term arg env
                 | uu____6868 ->
                     let uu____6883 = encode_args args_e env  in
                     (match uu____6883 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6952 = encode_term head1 env  in
                            match uu____6952 with
                            | (smt_head,decls') ->
                                let app_tm = mk_Apply_args smt_head args  in
                                (match ht_opt with
                                 | uu____6972 ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some
                                     (head_type,formals,c) ->
                                     ((let uu____7041 =
                                         FStar_TypeChecker_Env.debug
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (FStar_Options.Other "PartialApp")
                                          in
                                       if uu____7041
                                       then
                                         let uu____7045 =
                                           FStar_Syntax_Print.term_to_string
                                             head1
                                            in
                                         let uu____7047 =
                                           FStar_Syntax_Print.term_to_string
                                             head_type
                                            in
                                         let uu____7049 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", " formals
                                            in
                                         let uu____7052 =
                                           FStar_Syntax_Print.comp_to_string
                                             c
                                            in
                                         let uu____7054 =
                                           FStar_Syntax_Print.args_to_string
                                             args_e
                                            in
                                         FStar_Util.print5
                                           "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                           uu____7045 uu____7047 uu____7049
                                           uu____7052 uu____7054
                                       else ());
                                      (let uu____7059 =
                                         FStar_Util.first_N
                                           (FStar_List.length args_e) formals
                                          in
                                       match uu____7059 with
                                       | (formals1,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____7157  ->
                                                  fun uu____7158  ->
                                                    match (uu____7157,
                                                            uu____7158)
                                                    with
                                                    | ((bv,uu____7188),
                                                       (a,uu____7190)) ->
                                                        FStar_Syntax_Syntax.NT
                                                          (bv, a)) formals1
                                               args_e
                                              in
                                           let ty =
                                             let uu____7222 =
                                               FStar_Syntax_Util.arrow rest c
                                                in
                                             FStar_All.pipe_right uu____7222
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           ((let uu____7226 =
                                               FStar_TypeChecker_Env.debug
                                                 env.FStar_SMTEncoding_Env.tcenv
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____7226
                                             then
                                               let uu____7230 =
                                                 FStar_Syntax_Print.term_to_string
                                                   ty
                                                  in
                                               FStar_Util.print1
                                                 "Encoding partial application, after subst:\n\tty=%s\n"
                                                 uu____7230
                                             else ());
                                            (let uu____7235 =
                                               let uu____7248 =
                                                 FStar_List.fold_left2
                                                   (fun uu____7283  ->
                                                      fun uu____7284  ->
                                                        fun e  ->
                                                          match (uu____7283,
                                                                  uu____7284)
                                                          with
                                                          | ((t_hyps,decls1),
                                                             (bv,uu____7325))
                                                              ->
                                                              let t1 =
                                                                FStar_Syntax_Subst.subst
                                                                  subst1
                                                                  bv.FStar_Syntax_Syntax.sort
                                                                 in
                                                              let uu____7353
                                                                =
                                                                encode_term_pred
                                                                  FStar_Pervasives_Native.None
                                                                  t1 env e
                                                                 in
                                                              (match uu____7353
                                                               with
                                                               | (t_hyp,decls'1)
                                                                   ->
                                                                   ((
                                                                    let uu____7369
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7369
                                                                    then
                                                                    let uu____7373
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____7375
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7373
                                                                    uu____7375
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                   ([], []) formals1 args
                                                  in
                                               match uu____7248 with
                                               | (t_hyps,decls1) ->
                                                   let uu____7410 =
                                                     match smt_head.FStar_SMTEncoding_Term.tm
                                                     with
                                                     | FStar_SMTEncoding_Term.FreeV
                                                         uu____7419 ->
                                                         encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           head_type env
                                                           smt_head
                                                     | uu____7428 ->
                                                         (FStar_SMTEncoding_Util.mkTrue,
                                                           [])
                                                      in
                                                   (match uu____7410 with
                                                    | (t_head_hyp,decls'1) ->
                                                        let hyp =
                                                          FStar_SMTEncoding_Term.mk_and_l
                                                            (t_head_hyp ::
                                                            t_hyps)
                                                            FStar_Range.dummyRange
                                                           in
                                                        let uu____7444 =
                                                          encode_term_pred
                                                            FStar_Pervasives_Native.None
                                                            ty env app_tm
                                                           in
                                                        (match uu____7444
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
                                                             let uu____7466 =
                                                               let uu____7473
                                                                 =
                                                                 FStar_SMTEncoding_Term.fvs_subset_of
                                                                   cvars
                                                                   app_tm_vars
                                                                  in
                                                               if uu____7473
                                                               then
                                                                 ([app_tm],
                                                                   app_tm_vars)
                                                               else
                                                                 (let uu____7486
                                                                    =
                                                                    let uu____7488
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7488
                                                                     in
                                                                  if
                                                                    uu____7486
                                                                  then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                  else
                                                                    (
                                                                    (
                                                                    let uu____7501
                                                                    =
                                                                    let uu____7507
                                                                    =
                                                                    let uu____7509
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7509
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7507)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7501);
                                                                    ([],
                                                                    cvars)))
                                                                in
                                                             (match uu____7466
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
                                             match uu____7235 with
                                             | (vars,pattern,has_type,decls'')
                                                 ->
                                                 ((let uu____7556 =
                                                     FStar_TypeChecker_Env.debug
                                                       env.FStar_SMTEncoding_Env.tcenv
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____7556
                                                   then
                                                     let uu____7560 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         has_type
                                                        in
                                                     FStar_Util.print1
                                                       "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                       uu____7560
                                                   else ());
                                                  (let tkey_hash =
                                                     FStar_SMTEncoding_Term.hash_of_term
                                                       app_tm
                                                      in
                                                   let e_typing =
                                                     let uu____7568 =
                                                       let uu____7576 =
                                                         FStar_SMTEncoding_Term.mkForall
                                                           t0.FStar_Syntax_Syntax.pos
                                                           ([pattern], vars,
                                                             has_type)
                                                          in
                                                       let uu____7585 =
                                                         let uu____7587 =
                                                           let uu____7589 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm
                                                              in
                                                           FStar_Util.digest_of_string
                                                             uu____7589
                                                            in
                                                         Prims.op_Hat
                                                           "partial_app_typing_"
                                                           uu____7587
                                                          in
                                                       (uu____7576,
                                                         (FStar_Pervasives_Native.Some
                                                            "Partial app typing"),
                                                         uu____7585)
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____7568
                                                      in
                                                   let uu____7595 =
                                                     let uu____7598 =
                                                       let uu____7601 =
                                                         let uu____7604 =
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
                                                           decls'' uu____7604
                                                          in
                                                       FStar_List.append
                                                         decls' uu____7601
                                                        in
                                                     FStar_List.append decls
                                                       uu____7598
                                                      in
                                                   (app_tm, uu____7595))))))))
                             in
                          let encode_full_app fv =
                            let uu____7624 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____7624 with
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
                                   FStar_Syntax_Syntax.pos = uu____7667;
                                   FStar_Syntax_Syntax.vars = uu____7668;_},uu____7669)
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
                                   FStar_Syntax_Syntax.pos = uu____7676;
                                   FStar_Syntax_Syntax.vars = uu____7677;_},uu____7678)
                                ->
                                let uu____7683 =
                                  let uu____7684 =
                                    let uu____7689 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7689
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7684
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7683
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7719 =
                                  let uu____7720 =
                                    let uu____7725 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7725
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7720
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7719
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7754,(FStar_Util.Inl t1,uu____7756),uu____7757)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7804,(FStar_Util.Inr c,uu____7806),uu____7807)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7854 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let uu____7878 =
                                 let head_type2 =
                                   let uu____7900 =
                                     FStar_TypeChecker_Normalize.normalize_refinement
                                       [FStar_TypeChecker_Env.Weak;
                                       FStar_TypeChecker_Env.HNF;
                                       FStar_TypeChecker_Env.EraseUniverses]
                                       env.FStar_SMTEncoding_Env.tcenv
                                       head_type1
                                      in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.unrefine uu____7900
                                    in
                                 let uu____7903 =
                                   curried_arrow_formals_comp head_type2  in
                                 match uu____7903 with
                                 | (formals,c) ->
                                     if
                                       (FStar_List.length formals) <
                                         (FStar_List.length args)
                                     then
                                       let head_type3 =
                                         let uu____7954 =
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
                                           uu____7954
                                          in
                                       let uu____7955 =
                                         curried_arrow_formals_comp
                                           head_type3
                                          in
                                       (match uu____7955 with
                                        | (formals1,c1) ->
                                            (head_type3, formals1, c1))
                                     else (head_type2, formals, c)
                                  in
                               (match uu____7878 with
                                | (head_type2,formals,c) ->
                                    ((let uu____8038 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "PartialApp")
                                         in
                                      if uu____8038
                                      then
                                        let uu____8042 =
                                          FStar_Syntax_Print.term_to_string
                                            head_type2
                                           in
                                        let uu____8044 =
                                          FStar_Syntax_Print.binders_to_string
                                            ", " formals
                                           in
                                        let uu____8047 =
                                          FStar_Syntax_Print.args_to_string
                                            args_e
                                           in
                                        FStar_Util.print3
                                          "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                          uu____8042 uu____8044 uu____8047
                                      else ());
                                     (match head2.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.pos =
                                               uu____8057;
                                             FStar_Syntax_Syntax.vars =
                                               uu____8058;_},uu____8059)
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
                                      | uu____8077 ->
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
           let uu____8166 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8166 with
            | (bs1,body1,opening) ->
                let fallback uu____8189 =
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
                  let uu____8199 =
                    let uu____8200 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8200
                     in
                  let uu____8202 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8199, uu____8202)  in
                let is_impure rc =
                  let uu____8212 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8212 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8227 =
                          let uu____8240 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8240
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8227 with
                         | (t1,uu____8243,uu____8244) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____8262 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8262
                  then
                    let uu____8267 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8267
                  else
                    (let uu____8270 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8270
                     then
                       let uu____8275 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8275
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8283 =
                         let uu____8289 =
                           let uu____8291 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8291
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8289)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8283);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8296 =
                       (is_impure rc) &&
                         (let uu____8299 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8299)
                        in
                     if uu____8296
                     then fallback ()
                     else
                       (let uu____8308 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8308 with
                        | (vars,guards,envbody,decls,uu____8333) ->
                            let body2 =
                              let uu____8347 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8347
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____8352 = encode_term body2 envbody  in
                            (match uu____8352 with
                             | (body3,decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect
                                    in
                                 let uu____8365 =
                                   let uu____8374 = codomain_eff rc  in
                                   match uu____8374 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8393 = encode_term tfun env
                                          in
                                       (match uu____8393 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8365 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8427 =
                                          let uu____8438 =
                                            let uu____8439 =
                                              let uu____8444 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8444, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8439
                                             in
                                          ([], vars, uu____8438)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8427
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8452 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8468 =
                                              let uu____8471 =
                                                let uu____8482 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____8482
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8471
                                               in
                                            let uu____8509 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____8468, uu____8509)
                                         in
                                      (match uu____8452 with
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
                                           ((let uu____8532 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8532
                                             then
                                               let uu____8537 =
                                                 let uu____8539 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8539
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8549 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8537 uu____8549
                                             else ());
                                            (let uu____8554 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8554 with
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 ((let uu____8563 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8563
                                                   then
                                                     let uu____8568 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t1
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8568
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
                                                   let uu____8581 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8581
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8590 =
                                                     let uu____8598 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8598)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8590
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8612 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8620
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue))
                                                              in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8612
                                                             is_pure
                                                            in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8621 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax)
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym
                                                          in
                                                       let uu____8635 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                          in
                                                       [uu____8635]
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
                                                       let uu____8643 =
                                                         let uu____8644 =
                                                           let uu____8652 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8652,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8644
                                                          in
                                                       [uu____8643]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8667 =
                                                     let uu____8675 =
                                                       let uu____8676 =
                                                         let uu____8687 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8687)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8676
                                                        in
                                                     (uu____8675,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8667
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8701 =
                                                   let uu____8702 =
                                                     let uu____8705 =
                                                       let uu____8708 =
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
                                                         decls'' uu____8708
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8705
                                                      in
                                                   FStar_List.append decls
                                                     uu____8702
                                                    in
                                                 (f, uu____8701)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8711,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8712;
                          FStar_Syntax_Syntax.lbunivs = uu____8713;
                          FStar_Syntax_Syntax.lbtyp = uu____8714;
                          FStar_Syntax_Syntax.lbeff = uu____8715;
                          FStar_Syntax_Syntax.lbdef = uu____8716;
                          FStar_Syntax_Syntax.lbattrs = uu____8717;
                          FStar_Syntax_Syntax.lbpos = uu____8718;_}::uu____8719),uu____8720)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8754;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8756;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8758;
                FStar_Syntax_Syntax.lbpos = uu____8759;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false ,uu____8786::uu____8787),uu____8788) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____8811,lbs),uu____8813) ->
           let names1 =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb  ->
                     let uu____8866 = lb  in
                     match uu____8866 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____8873;
                         FStar_Syntax_Syntax.lbtyp = uu____8874;
                         FStar_Syntax_Syntax.lbeff = uu____8875;
                         FStar_Syntax_Syntax.lbdef = uu____8876;
                         FStar_Syntax_Syntax.lbattrs = uu____8877;
                         FStar_Syntax_Syntax.lbpos = uu____8878;_} ->
                         let x = FStar_Util.left lbname  in
                         let uu____8894 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname
                            in
                         let uu____8896 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         (uu____8894, uu____8896)))
              in
           FStar_Exn.raise (FStar_SMTEncoding_Env.Inner_let_rec names1)
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
              let uu____8954 =
                let uu____8959 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8959 env  in
              match uu____8954 with
              | (ee1,decls1) ->
                  let uu____8984 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8984 with
                   | (xs,e21) ->
                       let uu____9009 = FStar_List.hd xs  in
                       (match uu____9009 with
                        | (x1,uu____9027) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____9033 = encode_body e21 env'  in
                            (match uu____9033 with
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
            let uu____9063 =
              let uu____9071 =
                let uu____9072 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9072  in
              FStar_SMTEncoding_Env.gen_term_var env uu____9071  in
            match uu____9063 with
            | (scrsym,scr',env1) ->
                let uu____9082 = encode_term e env1  in
                (match uu____9082 with
                 | (scr,decls) ->
                     let uu____9093 =
                       let encode_branch b uu____9122 =
                         match uu____9122 with
                         | (else_case,decls1) ->
                             let uu____9141 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9141 with
                              | (p,w,br) ->
                                  let uu____9167 = encode_pat env1 p  in
                                  (match uu____9167 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9204  ->
                                                   match uu____9204 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9211 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9233 =
                                               encode_term w1 env2  in
                                             (match uu____9233 with
                                              | (w2,decls2) ->
                                                  let uu____9246 =
                                                    let uu____9247 =
                                                      let uu____9252 =
                                                        let uu____9253 =
                                                          let uu____9258 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9258)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9253
                                                         in
                                                      (guard, uu____9252)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9247
                                                     in
                                                  (uu____9246, decls2))
                                          in
                                       (match uu____9211 with
                                        | (guard1,decls2) ->
                                            let uu____9273 =
                                              encode_br br env2  in
                                            (match uu____9273 with
                                             | (br1,decls3) ->
                                                 let uu____9286 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9286,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9093 with
                      | (match_tm,decls1) ->
                          let uu____9307 =
                            let uu____9308 =
                              let uu____9319 =
                                let uu____9326 =
                                  let uu____9331 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9331, scr)  in
                                [uu____9326]  in
                              (uu____9319, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9308
                              FStar_Range.dummyRange
                             in
                          (uu____9307, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9354 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9354
       then
         let uu____9357 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9357
       else ());
      (let uu____9362 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9362 with
       | (vars,pat_term) ->
           let uu____9379 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9421  ->
                     fun v1  ->
                       match uu____9421 with
                       | (env1,vars1) ->
                           let uu____9457 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____9457 with
                            | (xx,uu____9476,env2) ->
                                let uu____9480 =
                                  let uu____9487 =
                                    let uu____9492 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____9492)  in
                                  uu____9487 :: vars1  in
                                (env2, uu____9480))) (env, []))
              in
           (match uu____9379 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9547 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9548 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9549 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9557 = encode_const c env1  in
                      (match uu____9557 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9565::uu____9566 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9570 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9593 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9593 with
                        | (uu____9601,uu____9602::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9607 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9643  ->
                                  match uu____9643 with
                                  | (arg,uu____9653) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9662 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9662))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9694) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9725 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9750 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9796  ->
                                  match uu____9796 with
                                  | (arg,uu____9812) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9821 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9821))
                         in
                      FStar_All.pipe_right uu____9750 FStar_List.flatten
                   in
                let pat_term1 uu____9852 = encode_term pat_term env1  in
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
      let uu____9862 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9910  ->
                fun uu____9911  ->
                  match (uu____9910, uu____9911) with
                  | ((tms,decls),(t,uu____9951)) ->
                      let uu____9978 = encode_term t env  in
                      (match uu____9978 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9862 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10056  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1382_10065 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1382_10065.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1382_10065.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1382_10065.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1382_10065.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1382_10065.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1382_10065.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1382_10065.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1382_10065.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1382_10065.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1382_10065.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1387_10082 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1387_10082.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1387_10082.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1387_10082.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1387_10082.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1387_10082.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1387_10082.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1387_10082.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1387_10082.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1387_10082.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1387_10082.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____10098 = FStar_Syntax_Util.head_and_args t  in
        match uu____10098 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10161::(x,uu____10163)::(t1,uu____10165)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10232 = encode_term x env1  in
                 (match uu____10232 with
                  | (x1,decls) ->
                      let uu____10243 = encode_term t1 env1  in
                      (match uu____10243 with
                       | (t2,decls') ->
                           let uu____10254 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10254, (FStar_List.append decls decls'))))
             | uu____10255 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10298  ->
             match uu____10298 with
             | (pats_l1,decls) ->
                 let uu____10343 =
                   FStar_List.fold_right
                     (fun uu____10378  ->
                        fun uu____10379  ->
                          match (uu____10378, uu____10379) with
                          | ((p,uu____10421),(pats1,decls1)) ->
                              let uu____10456 = encode_smt_pattern p  in
                              (match uu____10456 with
                               | (t,d) ->
                                   let uu____10471 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10471 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10488 =
                                            let uu____10494 =
                                              let uu____10496 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10498 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10496 uu____10498
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10494)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10488);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10343 with
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
        let uu____10558 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10558
        then
          let uu____10563 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10565 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10563 uu____10565
        else ()  in
      let enc f r l =
        let uu____10607 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10639 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10639 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10607 with
        | (decls,args) ->
            let uu____10670 =
              let uu___1451_10671 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1451_10671.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1451_10671.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10670, decls)
         in
      let const_op f r uu____10706 =
        let uu____10719 = f r  in (uu____10719, [])  in
      let un_op f l =
        let uu____10742 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10742  in
      let bin_op f uu___2_10762 =
        match uu___2_10762 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10773 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10814 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10839  ->
                 match uu____10839 with
                 | (t,uu____10855) ->
                     let uu____10860 = encode_formula t env  in
                     (match uu____10860 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10814 with
        | (decls,phis) ->
            let uu____10889 =
              let uu___1481_10890 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1481_10890.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1481_10890.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10889, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10953  ->
               match uu____10953 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10974) -> false
                    | uu____10977 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10996 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10996
        else
          (let uu____11013 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11013 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11081 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11113 =
                       let uu____11118 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11119 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11118, uu____11119)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11113
                 | uu____11120 -> failwith "Impossible")
             in
          uu____11081 r args
        else
          (let uu____11126 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11126)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11188 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11220 =
                       let uu____11225 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11226 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11225, uu____11226)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11220
                 | uu____11227 -> failwith "Impossible")
             in
          uu____11188 r args
        else
          (let uu____11233 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11233)
         in
      let mk_imp1 r uu___3_11262 =
        match uu___3_11262 with
        | (lhs,uu____11268)::(rhs,uu____11270)::[] ->
            let uu____11311 = encode_formula rhs env  in
            (match uu____11311 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11326) ->
                      (l1, decls1)
                  | uu____11331 ->
                      let uu____11332 = encode_formula lhs env  in
                      (match uu____11332 with
                       | (l2,decls2) ->
                           let uu____11343 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11343, (FStar_List.append decls1 decls2)))))
        | uu____11344 -> failwith "impossible"  in
      let mk_ite r uu___4_11372 =
        match uu___4_11372 with
        | (guard,uu____11378)::(_then,uu____11380)::(_else,uu____11382)::[]
            ->
            let uu____11439 = encode_formula guard env  in
            (match uu____11439 with
             | (g,decls1) ->
                 let uu____11450 = encode_formula _then env  in
                 (match uu____11450 with
                  | (t,decls2) ->
                      let uu____11461 = encode_formula _else env  in
                      (match uu____11461 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11473 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11503 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11503  in
      let connectives =
        let uu____11533 =
          let uu____11558 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11558)  in
        let uu____11601 =
          let uu____11628 =
            let uu____11653 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11653)  in
          let uu____11696 =
            let uu____11723 =
              let uu____11750 =
                let uu____11775 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11775)  in
              let uu____11818 =
                let uu____11845 =
                  let uu____11872 =
                    let uu____11897 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11897)  in
                  [uu____11872;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11845  in
              uu____11750 :: uu____11818  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11723  in
          uu____11628 :: uu____11696  in
        uu____11533 :: uu____11601  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12442 = encode_formula phi' env  in
            (match uu____12442 with
             | (phi2,decls) ->
                 let uu____12453 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12453, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12455 ->
            let uu____12462 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12462 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12501 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12501 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12513;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12515;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12517;
                 FStar_Syntax_Syntax.lbpos = uu____12518;_}::[]),e2)
            ->
            let uu____12545 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12545 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12598::(x,uu____12600)::(t,uu____12602)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12669 = encode_term x env  in
                 (match uu____12669 with
                  | (x1,decls) ->
                      let uu____12680 = encode_term t env  in
                      (match uu____12680 with
                       | (t1,decls') ->
                           let uu____12691 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12691, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12694)::(msg,uu____12696)::(phi2,uu____12698)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12765 =
                   let uu____12770 =
                     let uu____12771 = FStar_Syntax_Subst.compress r  in
                     uu____12771.FStar_Syntax_Syntax.n  in
                   let uu____12774 =
                     let uu____12775 = FStar_Syntax_Subst.compress msg  in
                     uu____12775.FStar_Syntax_Syntax.n  in
                   (uu____12770, uu____12774)  in
                 (match uu____12765 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12784))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12795 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12802)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12837 when head_redex env head2 ->
                 let uu____12852 = whnf env phi1  in
                 encode_formula uu____12852 env
             | uu____12853 ->
                 let uu____12868 = encode_term phi1 env  in
                 (match uu____12868 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12880 =
                          let uu____12882 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12883 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12882 uu____12883
                           in
                        if uu____12880
                        then tt
                        else
                          (let uu___1668_12887 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___1668_12887.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___1668_12887.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12888 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12888, decls)))
        | uu____12889 ->
            let uu____12890 = encode_term phi1 env  in
            (match uu____12890 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12902 =
                     let uu____12904 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12905 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12904 uu____12905  in
                   if uu____12902
                   then tt
                   else
                     (let uu___1676_12909 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1676_12909.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1676_12909.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12910 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12910, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12954 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12954 with
        | (vars,guards,env2,decls,uu____12993) ->
            let uu____13006 = encode_smt_patterns ps env2  in
            (match uu____13006 with
             | (pats,decls') ->
                 let uu____13043 = encode_formula body env2  in
                 (match uu____13043 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13075;
                             FStar_SMTEncoding_Term.rng = uu____13076;_}::[])::[]
                            when
                            let uu____13096 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13096 = gf -> []
                        | uu____13099 -> guards  in
                      let uu____13104 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13104, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13115 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13115 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13124 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13230  ->
                     match uu____13230 with
                     | (l,uu____13255) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13124 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13324,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13416 = encode_q_body env vars pats body  in
             match uu____13416 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13461 =
                     let uu____13472 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13472)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13461
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13503 = encode_q_body env vars pats body  in
             match uu____13503 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13547 =
                   let uu____13548 =
                     let uu____13559 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13559)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13548
                    in
                 (uu____13547, decls))))
