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
  = fun mname  -> fun r  -> mkForall_fuel' mname r Prims.int_one 
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
  
let (maybe_whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t' = whnf env t  in
      let uu____468 = FStar_Syntax_Util.head_and_args t'  in
      match uu____468 with
      | (head',uu____488) ->
          let uu____513 = head_redex env head'  in
          if uu____513
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____526 =
      let uu____527 = FStar_Syntax_Syntax.null_binder t  in [uu____527]  in
    let uu____546 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____526 uu____546 FStar_Pervasives_Native.None
  
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
                let uu____568 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____568 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____569 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____569
                | s ->
                    let uu____571 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____571) e)
  
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
          let uu____627 =
            let uu____633 =
              let uu____635 = FStar_Util.string_of_int arity  in
              let uu____637 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____635 uu____637
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____633)  in
          FStar_Errors.raise_error uu____627 rng
  
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
              | uu____725 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body)
               in
            let rec is_tot_fun_axioms ctx ctx_guard head2 vars1 guards1 =
              match (vars1, guards1) with
              | ([],[]) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____842::[],uu____843) ->
                  if is_pure
                  then
                    let uu____883 =
                      let uu____884 =
                        let uu____889 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2  in
                        (ctx_guard, uu____889)  in
                      FStar_SMTEncoding_Util.mkImp uu____884  in
                    maybe_mkForall [[head2]] ctx uu____883
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2,g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____941 =
                      let uu____942 =
                        let uu____947 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2  in
                        (ctx_guard, uu____947)  in
                      FStar_SMTEncoding_Util.mkImp uu____942  in
                    maybe_mkForall [[head2]] ctx uu____941  in
                  let app = mk_Apply head2 [x]  in
                  let ctx1 = FStar_List.append ctx [x]  in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x)  in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2  in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu____1006 -> failwith "impossible: isTotFun_axioms"  in
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
                  (let uu____1077 = FStar_Util.first_N arity args  in
                   match uu____1077 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1101 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____1101 arity n_args rng)
  
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
          let uu____1124 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____1124 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1133  ->
    match uu___1_1133 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1139 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1187;
                       FStar_SMTEncoding_Term.rng = uu____1188;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1219) ->
              let uu____1229 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1246 -> false) args (FStar_List.rev xs))
                 in
              if uu____1229
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f  in
                ((let uu____1255 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp")
                     in
                  if uu____1255
                  then
                    let uu____1260 = FStar_SMTEncoding_Term.print_smt_term t
                       in
                    let uu____1262 =
                      match n1 with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x
                       in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1260 uu____1262
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1272,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1276 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1284 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1284))
                 in
              if uu____1276
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1291 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____1309 'Auu____1310 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1309) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1310) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1368  ->
                  match uu____1368 with
                  | (x,uu____1374) ->
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
              let uu____1382 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1394 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1394) uu____1382 tl1
               in
            let uu____1397 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1424  ->
                      match uu____1424 with
                      | (b,uu____1431) ->
                          let uu____1432 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1432))
               in
            (match uu____1397 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1439) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____1453 =
                   let uu____1459 =
                     let uu____1461 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1461
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1459)  in
                 FStar_Errors.log_issue pos uu____1453)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1747 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1762 ->
            let uu____1769 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1769
        | uu____1771 ->
            if norm1
            then let uu____1773 = whnf env t1  in aux false uu____1773
            else
              (let uu____1777 =
                 let uu____1779 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1781 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1779 uu____1781
                  in
               failwith uu____1777)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1823) ->
        let uu____1828 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1828 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1849 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1849)
              | uu____1856 -> (args, res)))
    | uu____1857 ->
        let uu____1858 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1858)
  
let is_arithmetic_primitive :
  'Auu____1872 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1872 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1895::uu____1896::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1900::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1903 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1934 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1957 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1967 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1967)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____2009)::uu____2010::uu____2011::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____2062)::uu____2063::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2100 -> false
  
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
          let uu____2424 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2424, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2426 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2426, [])
      | FStar_Const.Const_char c1 ->
          let uu____2429 =
            let uu____2430 =
              let uu____2438 =
                let uu____2441 =
                  let uu____2442 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2442  in
                [uu____2441]  in
              ("FStar.Char.__char_of_int", uu____2438)  in
            FStar_SMTEncoding_Util.mkApp uu____2430  in
          (uu____2429, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2460 =
            let uu____2461 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2461  in
          (uu____2460, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2482) ->
          let uu____2485 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2485, [])
      | FStar_Const.Const_range uu____2486 ->
          let uu____2487 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2487, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2490 =
            let uu____2491 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2491  in
          (uu____2490, [])
      | c1 ->
          let uu____2493 =
            let uu____2495 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2495  in
          failwith uu____2493

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
        (let uu____2524 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2524
         then
           let uu____2527 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2527
         else ());
        (let uu____2533 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2615  ->
                   fun b  ->
                     match uu____2615 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2680 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2696 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2696 with
                           | (xxsym,xx,env') ->
                               let uu____2721 =
                                 let uu____2726 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2726 env1 xx
                                  in
                               (match uu____2721 with
                                | (guard_x_t,decls') ->
                                    let uu____2741 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2741, guard_x_t, env', decls', x))
                            in
                         (match uu____2680 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2533 with
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
          let uu____2841 = encode_term t env  in
          match uu____2841 with
          | (t1,decls) ->
              let uu____2852 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2852, decls)

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
          let uu____2863 = encode_term t env  in
          match uu____2863 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2878 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2878, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2880 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2880, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2886 = encode_args args_e env  in
        match uu____2886 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2905 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2927 = FStar_List.hd arg_tms1  in unbox uu____2927
               in
            let binary unbox arg_tms1 =
              let uu____2952 =
                let uu____2953 = FStar_List.hd arg_tms1  in unbox uu____2953
                 in
              let uu____2954 =
                let uu____2955 =
                  let uu____2956 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2956  in
                unbox uu____2955  in
              (uu____2952, uu____2954)  in
            let mk_default uu____2964 =
              let uu____2965 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2965 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____3054 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____3054
              then
                let uu____3057 =
                  let uu____3058 = mk_args ts  in op uu____3058  in
                FStar_All.pipe_right uu____3057 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____3116 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3116
              then
                let uu____3119 = binary unbox ts  in
                match uu____3119 with
                | (t1,t2) ->
                    let uu____3126 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3126 box
              else
                (let uu____3132 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3132
                 then
                   let uu____3135 =
                     let uu____3136 = binary unbox ts  in op uu____3136  in
                   FStar_All.pipe_right uu____3135 box
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
            let uu____3571 =
              let uu____3581 =
                FStar_List.tryFind
                  (fun uu____3605  ->
                     match uu____3605 with
                     | (l,uu____3616) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3581 FStar_Util.must  in
            (match uu____3571 with
             | (uu____3660,op) ->
                 let uu____3672 = op arg_tms  in (uu____3672, decls))

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
        let uu____3688 = FStar_List.hd args_e  in
        match uu____3688 with
        | (tm_sz,uu____3704) ->
            let uu____3713 = uu____3688  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3724 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3750::(sz_arg,uu____3752)::uu____3753::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3820 =
                    let uu____3821 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3821  in
                  let uu____3848 =
                    let uu____3852 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3852  in
                  (uu____3820, uu____3848)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3859::(sz_arg,uu____3861)::uu____3862::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3929 =
                    let uu____3931 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3931
                     in
                  failwith uu____3929
              | uu____3941 ->
                  let uu____3956 = FStar_List.tail args_e  in
                  (uu____3956, FStar_Pervasives_Native.None)
               in
            (match uu____3724 with
             | (arg_tms,ext_sz) ->
                 let uu____3983 = encode_args arg_tms env  in
                 (match uu____3983 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____4004 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____4016 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____4016  in
                      let unary_arith arg_tms2 =
                        let uu____4027 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____4027  in
                      let binary arg_tms2 =
                        let uu____4042 =
                          let uu____4043 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4043
                           in
                        let uu____4044 =
                          let uu____4045 =
                            let uu____4046 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4046  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4045
                           in
                        (uu____4042, uu____4044)  in
                      let binary_arith arg_tms2 =
                        let uu____4063 =
                          let uu____4064 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4064
                           in
                        let uu____4065 =
                          let uu____4066 =
                            let uu____4067 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4067  in
                          FStar_SMTEncoding_Term.unboxInt uu____4066  in
                        (uu____4063, uu____4065)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____4125 =
                          let uu____4126 = mk_args ts  in op uu____4126  in
                        FStar_All.pipe_right uu____4125 resBox  in
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
                        let uu____4258 =
                          let uu____4263 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4263  in
                        let uu____4272 =
                          let uu____4277 =
                            let uu____4279 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4279  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4277  in
                        mk_bv uu____4258 unary uu____4272 arg_tms2  in
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
                      let uu____4519 =
                        let uu____4529 =
                          FStar_List.tryFind
                            (fun uu____4553  ->
                               match uu____4553 with
                               | (l,uu____4564) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4529 FStar_Util.must  in
                      (match uu____4519 with
                       | (uu____4610,op) ->
                           let uu____4622 = op arg_tms1  in
                           (uu____4622, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___593_4632 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___593_4632.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___593_4632.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___593_4632.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___593_4632.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___593_4632.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___593_4632.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___593_4632.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___593_4632.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___593_4632.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___593_4632.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4634 = encode_term t env1  in
      match uu____4634 with
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
               (uu____4660,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4661;
                             FStar_SMTEncoding_Term.freevars = uu____4662;
                             FStar_SMTEncoding_Term.rng = uu____4663;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4664;
                  FStar_SMTEncoding_Term.freevars = uu____4665;
                  FStar_SMTEncoding_Term.rng = uu____4666;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4712 ->
               let uu____4713 = encode_formula t env1  in
               (match uu____4713 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4733 =
                            let uu____4738 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4738, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4733
                      | uu____4739 ->
                          let uu____4740 =
                            let uu____4751 =
                              let uu____4752 =
                                let uu____4757 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4757, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4752  in
                            ([[valid_tm]], vars, uu____4751)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4740
                       in
                    let ax =
                      let uu____4767 =
                        let uu____4775 =
                          let uu____4777 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4777  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4775)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4767  in
                    let uu____4783 =
                      let uu____4784 =
                        let uu____4787 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4787  in
                      FStar_List.append decls uu____4784  in
                    (tm, uu____4783)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let t0 = t1  in
      (let uu____4800 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4800
       then
         let uu____4805 = FStar_Syntax_Print.tag_of_term t1  in
         let uu____4807 = FStar_Syntax_Print.term_to_string t1  in
         FStar_Util.print2 "(%s)   %s\n" uu____4805 uu____4807
       else ());
      (match t1.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4816 ->
           let uu____4839 =
             let uu____4841 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4844 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4846 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4841
               uu____4844 uu____4846
              in
           failwith uu____4839
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4853 =
             let uu____4855 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4858 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4860 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4855
               uu____4858 uu____4860
              in
           failwith uu____4853
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4870 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4870
             then
               let uu____4875 = FStar_Syntax_Print.term_to_string t1  in
               let uu____4877 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4875
                 uu____4877
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4883 =
             let uu____4885 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4885
              in
           failwith uu____4883
       | FStar_Syntax_Syntax.Tm_ascribed (t2,(k,uu____4894),uu____4895) ->
           let uu____4944 =
             match k with
             | FStar_Util.Inl t3 -> FStar_Syntax_Util.is_unit t3
             | uu____4954 -> false  in
           if uu____4944
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t2 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4972) ->
           let tv =
             let uu____4978 =
               let uu____4985 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4985
                in
             uu____4978 t1.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4989 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4989
             then
               let uu____4994 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4996 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4994
                 uu____4996
             else ());
            (let t2 =
               let uu____5004 =
                 let uu____5015 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____5015]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____5004
                in
             encode_term t2 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t2,FStar_Syntax_Syntax.Meta_pattern uu____5041) ->
           encode_term t2
             (let uu___666_5067 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___666_5067.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___666_5067.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___666_5067.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___666_5067.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___666_5067.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___666_5067.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___666_5067.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___666_5067.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___666_5067.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___666_5067.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t2,uu____5070) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t2 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t2, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let encode_freev uu____5087 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v1.FStar_Syntax_Syntax.fv_name
                in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v1.FStar_Syntax_Syntax.fv_name
                in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
             let uu____5092 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu____5116 ->
                     let sym_name =
                       let uu____5127 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5127  in
                     let uu____5130 =
                       let uu____5133 =
                         let uu____5134 =
                           let uu____5142 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5142,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5134  in
                       [uu____5133]  in
                     (uu____5130, sym_name)
                 | FStar_SMTEncoding_Term.App (uu____5149,[]) ->
                     let sym_name =
                       let uu____5154 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5154  in
                     let uu____5157 =
                       let uu____5160 =
                         let uu____5161 =
                           let uu____5169 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5169,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5161  in
                       [uu____5160]  in
                     (uu____5157, sym_name)
                 | uu____5176 -> ([], "")
               else ([], "")  in
             match uu____5092 with
             | (aux_decls,sym_name) ->
                 let uu____5199 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls []
                    in
                 (tok, uu____5199)
              in
           let uu____5207 = head_redex env t1  in
           if uu____5207
           then
             let uu____5214 = maybe_whnf env t1  in
             (match uu____5214 with
              | FStar_Pervasives_Native.None  -> encode_freev ()
              | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu____5224 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5226) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5256 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5256 with
            | (binders1,res) ->
                let uu____5267 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5267
                then
                  let uu____5274 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5274 with
                   | (vars,guards_l,env',decls,uu____5299) ->
                       let fsym =
                         let uu____5313 =
                           let uu____5319 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5319, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5313  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5325 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___725_5334 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___725_5334.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___725_5334.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___725_5334.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___725_5334.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___725_5334.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___725_5334.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___725_5334.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___725_5334.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___725_5334.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___725_5334.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___725_5334.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___725_5334.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___725_5334.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___725_5334.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___725_5334.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___725_5334.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___725_5334.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___725_5334.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___725_5334.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___725_5334.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___725_5334.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___725_5334.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___725_5334.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___725_5334.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___725_5334.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___725_5334.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___725_5334.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___725_5334.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___725_5334.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___725_5334.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___725_5334.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___725_5334.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___725_5334.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___725_5334.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___725_5334.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___725_5334.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___725_5334.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___725_5334.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___725_5334.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___725_5334.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___725_5334.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___725_5334.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___725_5334.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___725_5334.FStar_TypeChecker_Env.erasable_types_tab)
                            }) res
                          in
                       (match uu____5325 with
                        | (pre_opt,res_t) ->
                            let uu____5346 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5346 with
                             | (res_pred,decls') ->
                                 let uu____5357 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5370 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5370, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5374 =
                                         encode_formula pre env'  in
                                       (match uu____5374 with
                                        | (guard,decls0) ->
                                            let uu____5387 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5387, decls0))
                                    in
                                 (match uu____5357 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        let uu____5402 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv)
                                           in
                                        FStar_All.pipe_right uu____5402
                                          FStar_Syntax_Util.is_pure_comp
                                         in
                                      let t_interp =
                                        let uu____5411 =
                                          let uu____5422 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5422)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          uu____5411
                                         in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t1.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure
                                           in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms)
                                         in
                                      let cvars =
                                        let uu____5444 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5444
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5463 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5465 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5463 <> uu____5465))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1)
                                         in
                                      let prefix1 =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_"  in
                                      let tkey_hash =
                                        let uu____5493 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix1 uu____5493  in
                                      let tsym =
                                        let uu____5497 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix1 uu____5497  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5511 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5511
                                        then
                                          let uu____5514 =
                                            let uu____5516 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5516 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5514
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t2 =
                                        let uu____5529 =
                                          let uu____5537 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5537)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5529
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5556 =
                                          let uu____5564 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5564,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5556
                                         in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t2
                                         in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t2
                                         in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym  in
                                        let uu____5581 =
                                          let uu____5589 =
                                            let uu____5590 =
                                              let uu____5601 =
                                                let uu____5602 =
                                                  let uu____5607 =
                                                    let uu____5608 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5608
                                                     in
                                                  (f_has_t, uu____5607)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5602
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5601)
                                               in
                                            let uu____5626 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5626 uu____5590  in
                                          (uu____5589,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5581
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5649 =
                                          let uu____5657 =
                                            let uu____5658 =
                                              let uu____5669 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5669)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5658
                                             in
                                          (uu____5657,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5649
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5692 =
                                        let uu____5693 =
                                          let uu____5696 =
                                            let uu____5699 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5699
                                             in
                                          FStar_List.append decls' uu____5696
                                           in
                                        FStar_List.append decls uu____5693
                                         in
                                      (t2, uu____5692)))))
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
                   let t2 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym  in
                     let uu____5720 =
                       let uu____5728 =
                         FStar_SMTEncoding_Term.mk_HasType t2
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5728,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5720  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t2  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5741 =
                       let uu____5749 =
                         let uu____5750 =
                           let uu____5761 =
                             let uu____5762 =
                               let uu____5767 =
                                 let uu____5768 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5768
                                  in
                               (f_has_t, uu____5767)  in
                             FStar_SMTEncoding_Util.mkImp uu____5762  in
                           ([[f_has_t]], [fsym], uu____5761)  in
                         let uu____5794 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5794 uu____5750  in
                       (uu____5749, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5741  in
                   let uu____5811 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t2, uu____5811)))
       | FStar_Syntax_Syntax.Tm_refine uu____5814 ->
           let uu____5821 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5831 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5831 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5840;
                 FStar_Syntax_Syntax.vars = uu____5841;_} ->
                 let uu____5848 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5848 with
                  | (b,f1) ->
                      let uu____5875 =
                        let uu____5876 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5876  in
                      (uu____5875, f1))
             | uu____5893 -> failwith "impossible"  in
           (match uu____5821 with
            | (x,f) ->
                let uu____5911 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5911 with
                 | (base_t,decls) ->
                     let uu____5922 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5922 with
                      | (x1,xtm,env') ->
                          let uu____5939 = encode_formula f env'  in
                          (match uu____5939 with
                           | (refinement,decls') ->
                               let uu____5950 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5950 with
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
                                      let uu____5978 =
                                        let uu____5989 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6000 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5989
                                          uu____6000
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5978
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____6054 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____6054 <> x1) &&
                                                (let uu____6058 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____6058 <> fsym)))
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
                                    ((let uu____6091 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____6091
                                      then
                                        let uu____6095 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____6097 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6095 tkey_hash uu____6097
                                      else ());
                                     (let tsym =
                                        let uu____6104 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____6104
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
                                      let t2 =
                                        let uu____6124 =
                                          let uu____6132 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____6132)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6124
                                         in
                                      let x_has_base_t =
                                        FStar_SMTEncoding_Term.mk_HasType xtm
                                          base_t
                                         in
                                      let x_has_t =
                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                          (FStar_Pervasives_Native.Some fterm)
                                          xtm t2
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let t_haseq_base =
                                        FStar_SMTEncoding_Term.mk_haseq
                                          base_t
                                         in
                                      let t_haseq_ref =
                                        FStar_SMTEncoding_Term.mk_haseq t2
                                         in
                                      let t_haseq1 =
                                        let uu____6152 =
                                          let uu____6160 =
                                            let uu____6161 =
                                              let uu____6172 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6172)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6161
                                             in
                                          (uu____6160,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6152
                                         in
                                      let t_kinding =
                                        let uu____6186 =
                                          let uu____6194 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6194,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6186
                                         in
                                      let t_interp =
                                        let uu____6208 =
                                          let uu____6216 =
                                            let uu____6217 =
                                              let uu____6228 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6228)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6217
                                             in
                                          (uu____6216,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6208
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1]  in
                                      let uu____6260 =
                                        let uu____6261 =
                                          let uu____6264 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6264
                                           in
                                        FStar_List.append decls uu____6261
                                         in
                                      (t2, uu____6260))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6268) ->
           let ttm =
             let uu____6286 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6286  in
           let uu____6288 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6288 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6300 =
                    let uu____6308 =
                      let uu____6310 =
                        let uu____6312 =
                          let uu____6314 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6314  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6312  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6310
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6308)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6300  in
                let uu____6320 =
                  let uu____6321 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6321  in
                (ttm, uu____6320))
       | FStar_Syntax_Syntax.Tm_app uu____6328 ->
           let uu____6345 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6345 with
            | (head1,args_e) ->
                let uu____6392 =
                  let uu____6409 = head_redex env head1  in
                  if uu____6409
                  then
                    let uu____6428 = maybe_whnf env t0  in
                    match uu____6428 with
                    | FStar_Pervasives_Native.None  -> (head1, args_e)
                    | FStar_Pervasives_Native.Some t2 ->
                        FStar_Syntax_Util.head_and_args t2
                  else (head1, args_e)  in
                (match uu____6392 with
                 | (head2,args_e1) ->
                     let uu____6504 =
                       let uu____6519 =
                         let uu____6520 = FStar_Syntax_Subst.compress head2
                            in
                         uu____6520.FStar_Syntax_Syntax.n  in
                       (uu____6519, args_e1)  in
                     (match uu____6504 with
                      | uu____6537 when is_arithmetic_primitive head2 args_e1
                          -> encode_arith_term env head2 args_e1
                      | uu____6560 when is_BitVector_primitive head2 args_e1
                          -> encode_BitVector_term env head2 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6578) when
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
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____6600;
                            FStar_Syntax_Syntax.vars = uu____6601;_},uu____6602),uu____6603)
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
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____6629;
                            FStar_Syntax_Syntax.vars = uu____6630;_},uu____6631),
                         (v0,uu____6633)::(v1,uu____6635)::(v2,uu____6637)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6708 = encode_term v0 env  in
                          (match uu____6708 with
                           | (v01,decls0) ->
                               let uu____6719 = encode_term v1 env  in
                               (match uu____6719 with
                                | (v11,decls1) ->
                                    let uu____6730 = encode_term v2 env  in
                                    (match uu____6730 with
                                     | (v21,decls2) ->
                                         let uu____6741 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6741,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_fvar
                         fv,(v0,uu____6744)::(v1,uu____6746)::(v2,uu____6748)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6815 = encode_term v0 env  in
                          (match uu____6815 with
                           | (v01,decls0) ->
                               let uu____6826 = encode_term v1 env  in
                               (match uu____6826 with
                                | (v11,decls1) ->
                                    let uu____6837 = encode_term v2 env  in
                                    (match uu____6837 with
                                     | (v21,decls2) ->
                                         let uu____6848 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6848,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of ),(arg,uu____6850)::[])
                          ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of
                         ),(arg,uu____6886)::(rng,uu____6888)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify ),uu____6939) ->
                          let e0 =
                            let uu____6961 = FStar_List.hd args_e1  in
                            FStar_TypeChecker_Util.reify_body_with_arg
                              env.FStar_SMTEncoding_Env.tcenv [] head2
                              uu____6961
                             in
                          ((let uu____6971 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify")
                               in
                            if uu____6971
                            then
                              let uu____6976 =
                                FStar_Syntax_Print.term_to_string e0  in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu____6976
                            else ());
                           (let e =
                              let uu____6984 =
                                let uu____6989 =
                                  FStar_TypeChecker_Util.remove_reify e0  in
                                let uu____6990 = FStar_List.tl args_e1  in
                                FStar_Syntax_Syntax.mk_Tm_app uu____6989
                                  uu____6990
                                 in
                              uu____6984 FStar_Pervasives_Native.None
                                t0.FStar_Syntax_Syntax.pos
                               in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect
                         uu____6999),(arg,uu____7001)::[]) ->
                          encode_term arg env
                      | uu____7036 ->
                          let uu____7051 = encode_args args_e1 env  in
                          (match uu____7051 with
                           | (args,decls) ->
                               let encode_partial_app ht_opt =
                                 let uu____7120 = encode_term head2 env  in
                                 match uu____7120 with
                                 | (smt_head,decls') ->
                                     let app_tm = mk_Apply_args smt_head args
                                        in
                                     (match ht_opt with
                                      | uu____7140 when
                                          Prims.int_one = Prims.int_one ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type,formals,c) ->
                                          ((let uu____7212 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp")
                                               in
                                            if uu____7212
                                            then
                                              let uu____7216 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2
                                                 in
                                              let uu____7218 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type
                                                 in
                                              let uu____7220 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals
                                                 in
                                              let uu____7223 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c
                                                 in
                                              let uu____7225 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1
                                                 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu____7216 uu____7218
                                                uu____7220 uu____7223
                                                uu____7225
                                            else ());
                                           (let uu____7230 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals
                                               in
                                            match uu____7230 with
                                            | (formals1,rest) ->
                                                let subst1 =
                                                  FStar_List.map2
                                                    (fun uu____7328  ->
                                                       fun uu____7329  ->
                                                         match (uu____7328,
                                                                 uu____7329)
                                                         with
                                                         | ((bv,uu____7359),
                                                            (a,uu____7361))
                                                             ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1
                                                   in
                                                let ty =
                                                  let uu____7393 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7393
                                                    (FStar_Syntax_Subst.subst
                                                       subst1)
                                                   in
                                                ((let uu____7397 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp")
                                                     in
                                                  if uu____7397
                                                  then
                                                    let uu____7401 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty
                                                       in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu____7401
                                                  else ());
                                                 (let uu____7406 =
                                                    let uu____7419 =
                                                      FStar_List.fold_left2
                                                        (fun uu____7454  ->
                                                           fun uu____7455  ->
                                                             fun e  ->
                                                               match 
                                                                 (uu____7454,
                                                                   uu____7455)
                                                               with
                                                               | ((t_hyps,decls1),
                                                                  (bv,uu____7496))
                                                                   ->
                                                                   let t2 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                   let uu____7524
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t2 env e
                                                                     in
                                                                   (match uu____7524
                                                                    with
                                                                    | 
                                                                    (t_hyp,decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu____7540
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7540
                                                                    then
                                                                    let uu____7544
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____7546
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7544
                                                                    uu____7546
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                        ([], []) formals1
                                                        args
                                                       in
                                                    match uu____7419 with
                                                    | (t_hyps,decls1) ->
                                                        let uu____7581 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu____7590 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu____7599 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                [])
                                                           in
                                                        (match uu____7581
                                                         with
                                                         | (t_head_hyp,decls'1)
                                                             ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7615 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm
                                                                in
                                                             (match uu____7615
                                                              with
                                                              | (has_type_conclusion,decls'')
                                                                  ->
                                                                  let has_type
                                                                    =
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
                                                                  let uu____7637
                                                                    =
                                                                    let uu____7644
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars
                                                                     in
                                                                    if
                                                                    uu____7644
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu____7657
                                                                    =
                                                                    let uu____7659
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7659
                                                                     in
                                                                    if
                                                                    uu____7657
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu____7672
                                                                    =
                                                                    let uu____7678
                                                                    =
                                                                    let uu____7680
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7680
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7678)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7672);
                                                                    ([],
                                                                    cvars)))
                                                                     in
                                                                  (match uu____7637
                                                                   with
                                                                   | 
                                                                   (pattern,vars)
                                                                    ->
                                                                    (vars,
                                                                    pattern,
                                                                    has_type,
                                                                    (FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls''))))))
                                                     in
                                                  match uu____7406 with
                                                  | (vars,pattern,has_type,decls'')
                                                      ->
                                                      ((let uu____7727 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp")
                                                           in
                                                        if uu____7727
                                                        then
                                                          let uu____7731 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type
                                                             in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu____7731
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm
                                                           in
                                                        let e_typing =
                                                          let uu____7739 =
                                                            let uu____7747 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern],
                                                                  vars,
                                                                  has_type)
                                                               in
                                                            let uu____7756 =
                                                              let uu____7758
                                                                =
                                                                let uu____7760
                                                                  =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm
                                                                   in
                                                                FStar_Util.digest_of_string
                                                                  uu____7760
                                                                 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu____7758
                                                               in
                                                            (uu____7747,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu____7756)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7739
                                                           in
                                                        let uu____7766 =
                                                          let uu____7769 =
                                                            let uu____7772 =
                                                              let uu____7775
                                                                =
                                                                FStar_SMTEncoding_Term.mk_decls
                                                                  ""
                                                                  tkey_hash
                                                                  [e_typing]
                                                                  (FStar_List.append
                                                                    decls
                                                                    (FStar_List.append
                                                                    decls'
                                                                    decls''))
                                                                 in
                                                              FStar_List.append
                                                                decls''
                                                                uu____7775
                                                               in
                                                            FStar_List.append
                                                              decls'
                                                              uu____7772
                                                             in
                                                          FStar_List.append
                                                            decls uu____7769
                                                           in
                                                        (app_tm, uu____7766)))))))
                                      | FStar_Pervasives_Native.None  ->
                                          failwith "impossible")
                                  in
                               let encode_full_app fv =
                                 let uu____7820 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv
                                    in
                                 match uu____7820 with
                                 | (fname,fuel_args,arity) ->
                                     let tm =
                                       maybe_curry_app
                                         t0.FStar_Syntax_Syntax.pos fname
                                         arity
                                         (FStar_List.append fuel_args args)
                                        in
                                     (tm, decls)
                                  in
                               let head3 = FStar_Syntax_Subst.compress head2
                                  in
                               let head_type =
                                 match head3.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_uinst
                                     ({
                                        FStar_Syntax_Syntax.n =
                                          FStar_Syntax_Syntax.Tm_name x;
                                        FStar_Syntax_Syntax.pos = uu____7863;
                                        FStar_Syntax_Syntax.vars = uu____7864;_},uu____7865)
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
                                        FStar_Syntax_Syntax.pos = uu____7872;
                                        FStar_Syntax_Syntax.vars = uu____7873;_},uu____7874)
                                     ->
                                     let uu____7879 =
                                       let uu____7880 =
                                         let uu____7885 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                            in
                                         FStar_All.pipe_right uu____7885
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7880
                                         FStar_Pervasives_Native.snd
                                        in
                                     FStar_Pervasives_Native.Some uu____7879
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu____7915 =
                                       let uu____7916 =
                                         let uu____7921 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                            in
                                         FStar_All.pipe_right uu____7921
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7916
                                         FStar_Pervasives_Native.snd
                                        in
                                     FStar_Pervasives_Native.Some uu____7915
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7950,(FStar_Util.Inl
                                                  t2,uu____7952),uu____7953)
                                     -> FStar_Pervasives_Native.Some t2
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____8000,(FStar_Util.Inr
                                                  c,uu____8002),uu____8003)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu____8050 -> FStar_Pervasives_Native.None
                                  in
                               (match head_type with
                                | FStar_Pervasives_Native.None  ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu____8074 =
                                      let head_type2 =
                                        let uu____8096 =
                                          FStar_TypeChecker_Normalize.normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1
                                           in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine
                                          uu____8096
                                         in
                                      let uu____8099 =
                                        curried_arrow_formals_comp head_type2
                                         in
                                      match uu____8099 with
                                      | (formals,c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu____8150 =
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
                                                uu____8150
                                               in
                                            let uu____8151 =
                                              curried_arrow_formals_comp
                                                head_type3
                                               in
                                            (match uu____8151 with
                                             | (formals1,c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c)
                                       in
                                    (match uu____8074 with
                                     | (head_type2,formals,c) ->
                                         ((let uu____8234 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp")
                                              in
                                           if uu____8234
                                           then
                                             let uu____8238 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2
                                                in
                                             let uu____8240 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals
                                                in
                                             let uu____8243 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1
                                                in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu____8238 uu____8240
                                               uu____8243
                                           else ());
                                          (match head3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8253;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8254;_},uu____8255)
                                               when
                                               (FStar_List.length formals) =
                                                 (FStar_List.length args)
                                               ->
                                               encode_full_app
                                                 fv.FStar_Syntax_Syntax.fv_name
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               (FStar_List.length formals) =
                                                 (FStar_List.length args)
                                               ->
                                               encode_full_app
                                                 fv.FStar_Syntax_Syntax.fv_name
                                           | uu____8273 ->
                                               if
                                                 (FStar_List.length formals)
                                                   > (FStar_List.length args)
                                               then
                                                 encode_partial_app
                                                   (FStar_Pervasives_Native.Some
                                                      (head_type2, formals,
                                                        c))
                                               else
                                                 encode_partial_app
                                                   FStar_Pervasives_Native.None))))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8362 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8362 with
            | (bs1,body1,opening) ->
                let fallback uu____8385 =
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
                  let uu____8395 =
                    let uu____8396 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8396
                     in
                  let uu____8398 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8395, uu____8398)  in
                let is_impure rc =
                  let uu____8408 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8408 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8423 =
                          let uu____8436 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8436
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8423 with
                         | (t2,uu____8439,uu____8440) -> t2)
                    | FStar_Pervasives_Native.Some t2 -> t2  in
                  let uu____8458 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8458
                  then
                    let uu____8463 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8463
                  else
                    (let uu____8466 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8466
                     then
                       let uu____8471 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8471
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8479 =
                         let uu____8485 =
                           let uu____8487 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8487
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8485)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8479);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8492 =
                       (is_impure rc) &&
                         (let uu____8495 =
                            FStar_SMTEncoding_Util.is_smt_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8495)
                        in
                     if uu____8492
                     then fallback ()
                     else
                       (let uu____8504 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8504 with
                        | (vars,guards,envbody,decls,uu____8529) ->
                            let body2 =
                              let uu____8543 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8543
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv [] body1
                              else body1  in
                            let uu____8548 = encode_term body2 envbody  in
                            (match uu____8548 with
                             | (body3,decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect
                                    in
                                 let uu____8561 =
                                   let uu____8570 = codomain_eff rc  in
                                   match uu____8570 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8589 = encode_term tfun env
                                          in
                                       (match uu____8589 with
                                        | (t2,decls1) ->
                                            ((FStar_Pervasives_Native.Some t2),
                                              decls1))
                                    in
                                 (match uu____8561 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8623 =
                                          let uu____8634 =
                                            let uu____8635 =
                                              let uu____8640 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8640, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8635
                                             in
                                          ([], vars, uu____8634)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8623
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8648 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t2 ->
                                            let uu____8664 =
                                              let uu____8667 =
                                                let uu____8678 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t2
                                                   in
                                                FStar_List.append uu____8678
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8667
                                               in
                                            let uu____8705 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t2)
                                               in
                                            (uu____8664, uu____8705)
                                         in
                                      (match uu____8648 with
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
                                           ((let uu____8728 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8728
                                             then
                                               let uu____8733 =
                                                 let uu____8735 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8735
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8745 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8733 uu____8745
                                             else ());
                                            (let uu____8750 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8750 with
                                             | FStar_Pervasives_Native.Some
                                                 t2 ->
                                                 ((let uu____8759 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8759
                                                   then
                                                     let uu____8764 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t2
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8764
                                                   else ());
                                                  (let decls1 =
                                                     FStar_List.append decls
                                                       (FStar_List.append
                                                          decls' decls'')
                                                      in
                                                   (t2, decls1)))
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 let cvar_sorts =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_sort
                                                     cvars1
                                                    in
                                                 let fsym =
                                                   let uu____8777 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8777
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8786 =
                                                     let uu____8794 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8794)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8786
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8808 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8816
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue))
                                                              in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8808
                                                             is_pure
                                                            in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8817 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax)
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym
                                                          in
                                                       let uu____8831 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                          in
                                                       [uu____8831]
                                                   | FStar_Pervasives_Native.Some
                                                       t2 ->
                                                       let f_has_t =
                                                         FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                           FStar_Pervasives_Native.None
                                                           f t2
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "typing_" fsym
                                                          in
                                                       let uu____8839 =
                                                         let uu____8840 =
                                                           let uu____8848 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8848,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8840
                                                          in
                                                       [uu____8839]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8863 =
                                                     let uu____8871 =
                                                       let uu____8872 =
                                                         let uu____8883 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8883)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8872
                                                        in
                                                     (uu____8871,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8863
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8897 =
                                                   let uu____8898 =
                                                     let uu____8901 =
                                                       let uu____8904 =
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
                                                         decls'' uu____8904
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8901
                                                      in
                                                   FStar_List.append decls
                                                     uu____8898
                                                    in
                                                 (f, uu____8897)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8907,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8908;
                          FStar_Syntax_Syntax.lbunivs = uu____8909;
                          FStar_Syntax_Syntax.lbtyp = uu____8910;
                          FStar_Syntax_Syntax.lbeff = uu____8911;
                          FStar_Syntax_Syntax.lbdef = uu____8912;
                          FStar_Syntax_Syntax.lbattrs = uu____8913;
                          FStar_Syntax_Syntax.lbpos = uu____8914;_}::uu____8915),uu____8916)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8950;
                FStar_Syntax_Syntax.lbtyp = t11;
                FStar_Syntax_Syntax.lbeff = uu____8952;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8954;
                FStar_Syntax_Syntax.lbpos = uu____8955;_}::[]),e2)
           -> encode_let x t11 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false ,uu____8982::uu____8983),uu____8984) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____9007,lbs),uu____9009) ->
           let names1 =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb  ->
                     let uu____9062 = lb  in
                     match uu____9062 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____9069;
                         FStar_Syntax_Syntax.lbtyp = uu____9070;
                         FStar_Syntax_Syntax.lbeff = uu____9071;
                         FStar_Syntax_Syntax.lbdef = uu____9072;
                         FStar_Syntax_Syntax.lbattrs = uu____9073;
                         FStar_Syntax_Syntax.lbpos = uu____9074;_} ->
                         let x = FStar_Util.left lbname  in
                         let uu____9090 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname
                            in
                         let uu____9092 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         (uu____9090, uu____9092)))
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
              let uu____9150 =
                let uu____9155 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9155 env  in
              match uu____9150 with
              | (ee1,decls1) ->
                  let uu____9180 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9180 with
                   | (xs,e21) ->
                       let uu____9205 = FStar_List.hd xs  in
                       (match uu____9205 with
                        | (x1,uu____9223) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____9229 = encode_body e21 env'  in
                            (match uu____9229 with
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
            let uu____9259 =
              let uu____9267 =
                let uu____9268 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9268  in
              FStar_SMTEncoding_Env.gen_term_var env uu____9267  in
            match uu____9259 with
            | (scrsym,scr',env1) ->
                let uu____9278 = encode_term e env1  in
                (match uu____9278 with
                 | (scr,decls) ->
                     let uu____9289 =
                       let encode_branch b uu____9318 =
                         match uu____9318 with
                         | (else_case,decls1) ->
                             let uu____9337 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9337 with
                              | (p,w,br) ->
                                  let uu____9363 = encode_pat env1 p  in
                                  (match uu____9363 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9400  ->
                                                   match uu____9400 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9407 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9429 =
                                               encode_term w1 env2  in
                                             (match uu____9429 with
                                              | (w2,decls2) ->
                                                  let uu____9442 =
                                                    let uu____9443 =
                                                      let uu____9448 =
                                                        let uu____9449 =
                                                          let uu____9454 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9454)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9449
                                                         in
                                                      (guard, uu____9448)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9443
                                                     in
                                                  (uu____9442, decls2))
                                          in
                                       (match uu____9407 with
                                        | (guard1,decls2) ->
                                            let uu____9469 =
                                              encode_br br env2  in
                                            (match uu____9469 with
                                             | (br1,decls3) ->
                                                 let uu____9482 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9482,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9289 with
                      | (match_tm,decls1) ->
                          let uu____9503 =
                            let uu____9504 =
                              let uu____9515 =
                                let uu____9522 =
                                  let uu____9527 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9527, scr)  in
                                [uu____9522]  in
                              (uu____9515, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9504
                              FStar_Range.dummyRange
                             in
                          (uu____9503, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9550 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9550
       then
         let uu____9553 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9553
       else ());
      (let uu____9558 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9558 with
       | (vars,pat_term) ->
           let uu____9575 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9617  ->
                     fun v1  ->
                       match uu____9617 with
                       | (env1,vars1) ->
                           let uu____9653 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____9653 with
                            | (xx,uu____9672,env2) ->
                                let uu____9676 =
                                  let uu____9683 =
                                    let uu____9688 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____9688)  in
                                  uu____9683 :: vars1  in
                                (env2, uu____9676))) (env, []))
              in
           (match uu____9575 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9743 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9744 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9745 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9753 = encode_const c env1  in
                      (match uu____9753 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9761::uu____9762 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9766 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9789 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9789 with
                        | (uu____9797,uu____9798::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9803 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9839  ->
                                  match uu____9839 with
                                  | (arg,uu____9849) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9858 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9858))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9890) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9921 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9946 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9992  ->
                                  match uu____9992 with
                                  | (arg,uu____10008) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10017 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10017))
                         in
                      FStar_All.pipe_right uu____9946 FStar_List.flatten
                   in
                let pat_term1 uu____10048 = encode_term pat_term env1  in
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
      let uu____10058 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10106  ->
                fun uu____10107  ->
                  match (uu____10106, uu____10107) with
                  | ((tms,decls),(t,uu____10147)) ->
                      let uu____10174 = encode_term t env  in
                      (match uu____10174 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10058 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10252  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1401_10261 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1401_10261.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1401_10261.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1401_10261.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1401_10261.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1401_10261.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1401_10261.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1401_10261.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1401_10261.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1401_10261.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1401_10261.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1406_10278 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1406_10278.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1406_10278.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1406_10278.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1406_10278.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1406_10278.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1406_10278.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1406_10278.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1406_10278.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1406_10278.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1406_10278.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____10294 = FStar_Syntax_Util.head_and_args t  in
        match uu____10294 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10357::(x,uu____10359)::(t1,uu____10361)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10428 = encode_term x env1  in
                 (match uu____10428 with
                  | (x1,decls) ->
                      let uu____10439 = encode_term t1 env1  in
                      (match uu____10439 with
                       | (t2,decls') ->
                           let uu____10450 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10450, (FStar_List.append decls decls'))))
             | uu____10451 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10494  ->
             match uu____10494 with
             | (pats_l1,decls) ->
                 let uu____10539 =
                   FStar_List.fold_right
                     (fun uu____10574  ->
                        fun uu____10575  ->
                          match (uu____10574, uu____10575) with
                          | ((p,uu____10617),(pats1,decls1)) ->
                              let uu____10652 = encode_smt_pattern p  in
                              (match uu____10652 with
                               | (t,d) ->
                                   let uu____10667 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10667 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10684 =
                                            let uu____10690 =
                                              let uu____10692 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10694 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10692 uu____10694
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10690)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10684);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10539 with
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
        let uu____10754 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10754
        then
          let uu____10759 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10761 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10759 uu____10761
        else ()  in
      let enc f r l =
        let uu____10803 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10835 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10835 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10803 with
        | (decls,args) ->
            let uu____10866 =
              let uu___1470_10867 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1470_10867.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1470_10867.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10866, decls)
         in
      let const_op f r uu____10902 =
        let uu____10915 = f r  in (uu____10915, [])  in
      let un_op f l =
        let uu____10938 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10938  in
      let bin_op f uu___2_10958 =
        match uu___2_10958 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10969 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11010 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11035  ->
                 match uu____11035 with
                 | (t,uu____11051) ->
                     let uu____11056 = encode_formula t env  in
                     (match uu____11056 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11010 with
        | (decls,phis) ->
            let uu____11085 =
              let uu___1500_11086 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1500_11086.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1500_11086.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11085, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11149  ->
               match uu____11149 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11170) -> false
                    | uu____11173 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu____11192 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11192
        else
          (let uu____11209 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11209 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.of_int (4))
        then
          let uu____11277 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11309 =
                       let uu____11314 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11315 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11314, uu____11315)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11309
                 | uu____11316 -> failwith "Impossible")
             in
          uu____11277 r args
        else
          (let uu____11322 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11322)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.of_int (4))
        then
          let uu____11384 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11416 =
                       let uu____11421 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11422 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11421, uu____11422)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11416
                 | uu____11423 -> failwith "Impossible")
             in
          uu____11384 r args
        else
          (let uu____11429 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11429)
         in
      let mk_imp1 r uu___3_11458 =
        match uu___3_11458 with
        | (lhs,uu____11464)::(rhs,uu____11466)::[] ->
            let uu____11507 = encode_formula rhs env  in
            (match uu____11507 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11522) ->
                      (l1, decls1)
                  | uu____11527 ->
                      let uu____11528 = encode_formula lhs env  in
                      (match uu____11528 with
                       | (l2,decls2) ->
                           let uu____11539 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11539, (FStar_List.append decls1 decls2)))))
        | uu____11540 -> failwith "impossible"  in
      let mk_ite r uu___4_11568 =
        match uu___4_11568 with
        | (guard,uu____11574)::(_then,uu____11576)::(_else,uu____11578)::[]
            ->
            let uu____11635 = encode_formula guard env  in
            (match uu____11635 with
             | (g,decls1) ->
                 let uu____11646 = encode_formula _then env  in
                 (match uu____11646 with
                  | (t,decls2) ->
                      let uu____11657 = encode_formula _else env  in
                      (match uu____11657 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11669 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11699 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11699  in
      let connectives =
        let uu____11729 =
          let uu____11754 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11754)  in
        let uu____11797 =
          let uu____11824 =
            let uu____11849 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11849)  in
          let uu____11892 =
            let uu____11919 =
              let uu____11946 =
                let uu____11971 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11971)  in
              let uu____12014 =
                let uu____12041 =
                  let uu____12068 =
                    let uu____12093 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12093)  in
                  [uu____12068;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12041  in
              uu____11946 :: uu____12014  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11919  in
          uu____11824 :: uu____11892  in
        uu____11729 :: uu____11797  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12638 = encode_formula phi' env  in
            (match uu____12638 with
             | (phi2,decls) ->
                 let uu____12649 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12649, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12651 ->
            let uu____12658 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12658 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12697 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12697 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12709;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12711;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12713;
                 FStar_Syntax_Syntax.lbpos = uu____12714;_}::[]),e2)
            ->
            let uu____12741 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12741 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12794::(x,uu____12796)::(t,uu____12798)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12865 = encode_term x env  in
                 (match uu____12865 with
                  | (x1,decls) ->
                      let uu____12876 = encode_term t env  in
                      (match uu____12876 with
                       | (t1,decls') ->
                           let uu____12887 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12887, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12890)::(msg,uu____12892)::(phi2,uu____12894)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12961 =
                   let uu____12966 =
                     let uu____12967 = FStar_Syntax_Subst.compress r  in
                     uu____12967.FStar_Syntax_Syntax.n  in
                   let uu____12970 =
                     let uu____12971 = FStar_Syntax_Subst.compress msg  in
                     uu____12971.FStar_Syntax_Syntax.n  in
                   (uu____12966, uu____12970)  in
                 (match uu____12961 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12980))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12991 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12998)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____13033 ->
                 let encode_valid uu____13057 =
                   let uu____13058 = encode_term phi1 env  in
                   match uu____13058 with
                   | (tt,decls) ->
                       let tt1 =
                         let uu____13070 =
                           let uu____13072 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng
                              in
                           let uu____13073 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos
                              in
                           FStar_Range.rng_included uu____13072 uu____13073
                            in
                         if uu____13070
                         then tt
                         else
                           (let uu___1688_13077 = tt  in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___1688_13077.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___1688_13077.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            })
                          in
                       let uu____13078 = FStar_SMTEncoding_Term.mk_Valid tt1
                          in
                       (uu____13078, decls)
                    in
                 let uu____13079 = head_redex env head2  in
                 if uu____13079
                 then
                   let uu____13086 = maybe_whnf env head2  in
                   (match uu____13086 with
                    | FStar_Pervasives_Native.None  -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu____13096 ->
            let uu____13097 = encode_term phi1 env  in
            (match uu____13097 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____13109 =
                     let uu____13111 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____13112 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____13111 uu____13112  in
                   if uu____13109
                   then tt
                   else
                     (let uu___1700_13116 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1700_13116.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1700_13116.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____13117 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____13117, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13161 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13161 with
        | (vars,guards,env2,decls,uu____13200) ->
            let uu____13213 = encode_smt_patterns ps env2  in
            (match uu____13213 with
             | (pats,decls') ->
                 let uu____13250 = encode_formula body env2  in
                 (match uu____13250 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13282;
                             FStar_SMTEncoding_Term.rng = uu____13283;_}::[])::[]
                            when
                            let uu____13303 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13303 = gf -> []
                        | uu____13306 -> guards  in
                      let uu____13311 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13311, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13322 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13322 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13331 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13437  ->
                     match uu____13437 with
                     | (l,uu____13462) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13331 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13531,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13623 = encode_q_body env vars pats body  in
             match uu____13623 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13668 =
                     let uu____13679 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13679)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13668
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13710 = encode_q_body env vars pats body  in
             match uu____13710 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13754 =
                   let uu____13755 =
                     let uu____13766 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13766)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13755
                    in
                 (uu____13754, decls))))
