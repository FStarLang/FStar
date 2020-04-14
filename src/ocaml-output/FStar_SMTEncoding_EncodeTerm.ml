open Prims
let mkForall_fuel' :
  'uuuuuu14 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu14 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n  ->
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
                     let add_fuel tms =
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
                     let pats1 = FStar_List.map add_fuel pats  in
                     let body1 =
                       match body.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                           let guard1 =
                             match guard.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.And ,guards) ->
                                 let uu____144 = add_fuel guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____144
                             | uu____147 ->
                                 let uu____148 = add_fuel [guard]  in
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
  
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        let uu____443 =
          let uu____447 =
            let uu____449 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____449  in
          FStar_Pervasives_Native.Some uu____447  in
        FStar_Profiling.profile
          (fun uu____452  ->
             FStar_TypeChecker_Normalize.normalize steps env t) uu____443
          "FStar.TypeChecker.SMTEncoding.EncodeTerm.norm_with_steps"
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        let uu____470 =
          let uu____474 =
            let uu____476 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____476  in
          FStar_Pervasives_Native.Some uu____474  in
        FStar_Profiling.profile
          (fun uu____479  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t)
          uu____470
          "FStar.TypeChecker.SMTEncoding.EncodeTerm.normalize_refinement"
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____492 = head_normal env t  in
      if uu____492
      then t
      else
        norm_with_steps
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
      norm_with_steps
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
      let uu____522 = FStar_Syntax_Util.head_and_args t'  in
      match uu____522 with
      | (head',uu____542) ->
          let uu____567 = head_redex env head'  in
          if uu____567
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____580 =
      let uu____581 = FStar_Syntax_Syntax.null_binder t  in [uu____581]  in
    let uu____600 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____580 uu____600 FStar_Pervasives_Native.None
  
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
                let uu____622 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____622 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____623 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____623
                | s ->
                    let uu____625 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____625) e)
  
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
  fun head  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____681 =
            let uu____687 =
              let uu____689 = FStar_Util.string_of_int arity  in
              let uu____691 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head uu____689 uu____691
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____687)  in
          FStar_Errors.raise_error uu____681 rng
  
let (isTotFun_axioms :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.fvs ->
        FStar_SMTEncoding_Term.term Prims.list ->
          Prims.bool -> FStar_SMTEncoding_Term.term)
  =
  fun pos  ->
    fun head  ->
      fun vars  ->
        fun guards  ->
          fun is_pure  ->
            let maybe_mkForall pat vars1 body =
              match vars1 with
              | [] -> body
              | uu____779 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body)
               in
            let rec is_tot_fun_axioms ctx ctx_guard head1 vars1 guards1 =
              match (vars1, guards1) with
              | ([],[]) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____896::[],uu____897) ->
                  if is_pure
                  then
                    let uu____937 =
                      let uu____938 =
                        let uu____943 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head1  in
                        (ctx_guard, uu____943)  in
                      FStar_SMTEncoding_Util.mkImp uu____938  in
                    maybe_mkForall [[head1]] ctx uu____937
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2,g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____995 =
                      let uu____996 =
                        let uu____1001 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head1  in
                        (ctx_guard, uu____1001)  in
                      FStar_SMTEncoding_Util.mkImp uu____996  in
                    maybe_mkForall [[head1]] ctx uu____995  in
                  let app = mk_Apply head1 [x]  in
                  let ctx1 = FStar_List.append ctx [x]  in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x)  in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2  in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu____1060 -> failwith "impossible: isTotFun_axioms"  in
            is_tot_fun_axioms [] FStar_SMTEncoding_Util.mkTrue head vars
              guards
  
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term) FStar_Util.either
      ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          match head with
          | FStar_Util.Inr head1 -> mk_Apply_args head1 args
          | FStar_Util.Inl head1 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head1, args)
              else
                if n_args > arity
                then
                  (let uu____1131 = FStar_Util.first_N arity args  in
                   match uu____1131 with
                   | (args1,rest) ->
                       let head2 =
                         FStar_SMTEncoding_Util.mkApp' (head1, args1)  in
                       mk_Apply_args head2 rest)
                else
                  (let uu____1155 = FStar_SMTEncoding_Term.op_to_string head1
                      in
                   raise_arity_mismatch uu____1155 arity n_args rng)
  
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
          let uu____1178 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____1178 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1187  ->
    match uu___1_1187 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1193 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1241;
                       FStar_SMTEncoding_Term.rng = uu____1242;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1273) ->
              let uu____1283 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1300 -> false) args (FStar_List.rev xs))
                 in
              if uu____1283
              then
                let n = FStar_SMTEncoding_Env.tok_of_name env f  in
                ((let uu____1309 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp")
                     in
                  if uu____1309
                  then
                    let uu____1314 = FStar_SMTEncoding_Term.print_smt_term t
                       in
                    let uu____1316 =
                      match n with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x
                       in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1314 uu____1316
                  else ());
                 n)
              else FStar_Pervasives_Native.None
          | (uu____1326,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1330 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1338 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1338))
                 in
              if uu____1330
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1345 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'uuuuuu1363 'uuuuuu1364 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1363) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1364) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1422  ->
                  match uu____1422 with
                  | (x,uu____1428) ->
                      norm_with_steps
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd::tl ->
            let pat_vars =
              let uu____1436 = FStar_Syntax_Free.names hd  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1448 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1448) uu____1436 tl
               in
            let uu____1451 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1478  ->
                      match uu____1478 with
                      | (b,uu____1485) ->
                          let uu____1486 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1486))
               in
            (match uu____1451 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1493) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd.FStar_Syntax_Syntax.pos tl
                    in
                 let uu____1507 =
                   let uu____1513 =
                     let uu____1515 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1515
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1513)  in
                 FStar_Errors.log_issue pos uu____1507)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1801 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1816 ->
            let uu____1823 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1823
        | uu____1825 ->
            if norm1
            then let uu____1827 = whnf env t1  in aux false uu____1827
            else
              (let uu____1831 =
                 let uu____1833 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1835 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1833 uu____1835
                  in
               failwith uu____1831)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1877) ->
        let uu____1882 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1882 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1903 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1903)
              | uu____1910 -> (args, res)))
    | uu____1911 ->
        let uu____1912 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1912)
  
let is_arithmetic_primitive :
  'uuuuuu1926 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'uuuuuu1926 Prims.list -> Prims.bool
  =
  fun head  ->
    fun args  ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1949::uu____1950::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1954::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1957 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n,FStar_Pervasives_Native.None )) -> true
    | uu____1988 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n
    | uu____2011 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'uuuuuu2021 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'uuuuuu2021)
        Prims.list -> Prims.bool
  =
  fun head  ->
    fun args  ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____2063)::uu____2064::uu____2065::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____2116)::uu____2117::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2154 -> false
  
let (encode_string_const : Prims.string -> FStar_SMTEncoding_Term.term) =
  fun s  ->
    let rec aux acc i bs =
      let uu____2194 =
        let uu____2196 = FStar_Compiler_Bytes.length bs  in i = uu____2196
         in
      if uu____2194
      then acc
      else
        (let acc1 =
           let uu____2203 =
             let uu____2204 =
               FStar_All.pipe_right (Prims.of_int (256))
                 FStar_BigInt.of_int_fs
                in
             FStar_BigInt.mult_big_int uu____2204 acc  in
           let uu____2207 =
             let uu____2208 = FStar_Compiler_Bytes.get bs i  in
             FStar_All.pipe_right uu____2208 FStar_BigInt.of_int_fs  in
           FStar_BigInt.add_big_int uu____2203 uu____2207  in
         aux acc1 (i + Prims.int_one) bs)
       in
    let id =
      let uu____2213 = FStar_Compiler_Bytes.string_as_utf8_bytes s  in
      aux FStar_BigInt.zero Prims.int_zero uu____2213  in
    let uu____2215 = FStar_SMTEncoding_Util.mk_String_const id  in
    FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2215
  
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
          let uu____2526 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2526, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2528 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2528, [])
      | FStar_Const.Const_char c1 ->
          let uu____2531 =
            let uu____2532 =
              let uu____2540 =
                let uu____2543 =
                  let uu____2544 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2544  in
                [uu____2543]  in
              ("FStar.Char.__char_of_int", uu____2540)  in
            FStar_SMTEncoding_Util.mkApp uu____2532  in
          (uu____2531, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2562 =
            let uu____2563 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2563  in
          (uu____2562, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2584) ->
          let uu____2587 = encode_string_const s  in (uu____2587, [])
      | FStar_Const.Const_range uu____2588 ->
          let uu____2589 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2589, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2592 =
            let uu____2593 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2593  in
          (uu____2592, [])
      | c1 ->
          let uu____2595 =
            let uu____2597 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2597  in
          failwith uu____2595

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
        (let uu____2626 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2626
         then
           let uu____2629 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2629
         else ());
        (let uu____2635 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2717  ->
                   fun b  ->
                     match uu____2717 with
                     | (vars,guards,env1,decls,names) ->
                         let uu____2782 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2798 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2798 with
                           | (xxsym,xx,env') ->
                               let uu____2823 =
                                 let uu____2828 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2828 env1 xx
                                  in
                               (match uu____2823 with
                                | (guard_x_t,decls') ->
                                    let uu____2843 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2843, guard_x_t, env', decls', x))
                            in
                         (match uu____2782 with
                          | (v,g,env2,decls',n) ->
                              ((v :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], []))
            in
         match uu____2635 with
         | (vars,guards,env1,decls,names) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names)))

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
          let uu____2943 = encode_term t env  in
          match uu____2943 with
          | (t1,decls) ->
              let uu____2954 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2954, decls)

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
          let uu____2965 = encode_term t env  in
          match uu____2965 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2980 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2980, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2982 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2982, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head  ->
      fun args_e  ->
        let uu____2988 = encode_args args_e env  in
        match uu____2988 with
        | (arg_tms,decls) ->
            let head_fv =
              match head.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3007 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____3029 = FStar_List.hd arg_tms1  in unbox uu____3029
               in
            let binary unbox arg_tms1 =
              let uu____3054 =
                let uu____3055 = FStar_List.hd arg_tms1  in unbox uu____3055
                 in
              let uu____3056 =
                let uu____3057 =
                  let uu____3058 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____3058  in
                unbox uu____3057  in
              (uu____3054, uu____3056)  in
            let mk_default uu____3066 =
              let uu____3067 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3067 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____3156 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____3156
              then
                let uu____3159 =
                  let uu____3160 = mk_args ts  in op uu____3160  in
                FStar_All.pipe_right uu____3159 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____3218 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3218
              then
                let uu____3221 = binary unbox ts  in
                match uu____3221 with
                | (t1,t2) ->
                    let uu____3228 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3228 box
              else
                (let uu____3234 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3234
                 then
                   let uu____3237 =
                     let uu____3238 = binary unbox ts  in op uu____3238  in
                   FStar_All.pipe_right uu____3237 box
                 else mk_default ())
               in
            let add box unbox =
              mk_l box FStar_SMTEncoding_Util.mkAdd (binary unbox)  in
            let sub box unbox =
              mk_l box FStar_SMTEncoding_Util.mkSub (binary unbox)  in
            let minus box unbox =
              mk_l box FStar_SMTEncoding_Util.mkMinus (unary unbox)  in
            let mul box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkMul  in
            let div box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkDiv  in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition,
                 (add FStar_SMTEncoding_Term.boxInt
                    FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Subtraction,
                (sub FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Multiply,
                (mul FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_mul"));
              (FStar_Parser_Const.op_Division,
                (div FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_div"));
              (FStar_Parser_Const.op_Modulus,
                (modulus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Minus,
                (minus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.real_op_Addition,
                (add FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Subtraction,
                (sub FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Multiply,
                (mul FStar_SMTEncoding_Term.boxReal
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
            let uu____3673 =
              let uu____3683 =
                FStar_List.tryFind
                  (fun uu____3707  ->
                     match uu____3707 with
                     | (l,uu____3718) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3683 FStar_Util.must  in
            (match uu____3673 with
             | (uu____3762,op) ->
                 let uu____3774 = op arg_tms  in (uu____3774, decls))

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
    fun head  ->
      fun args_e  ->
        let uu____3790 = FStar_List.hd args_e  in
        match uu____3790 with
        | (tm_sz,uu____3806) ->
            let uu____3815 = uu____3790  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls []  in
            let uu____3826 =
              match ((head.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3852::(sz_arg,uu____3854)::uu____3855::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3922 =
                    let uu____3923 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3923  in
                  let uu____3950 =
                    let uu____3954 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3954  in
                  (uu____3922, uu____3950)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3961::(sz_arg,uu____3963)::uu____3964::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____4031 =
                    let uu____4033 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____4033
                     in
                  failwith uu____4031
              | uu____4043 ->
                  let uu____4058 = FStar_List.tail args_e  in
                  (uu____4058, FStar_Pervasives_Native.None)
               in
            (match uu____3826 with
             | (arg_tms,ext_sz) ->
                 let uu____4085 = encode_args arg_tms env  in
                 (match uu____4085 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____4106 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____4118 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____4118  in
                      let unary_arith arg_tms2 =
                        let uu____4129 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____4129  in
                      let binary arg_tms2 =
                        let uu____4144 =
                          let uu____4145 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4145
                           in
                        let uu____4146 =
                          let uu____4147 =
                            let uu____4148 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4148  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4147
                           in
                        (uu____4144, uu____4146)  in
                      let binary_arith arg_tms2 =
                        let uu____4165 =
                          let uu____4166 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4166
                           in
                        let uu____4167 =
                          let uu____4168 =
                            let uu____4169 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4169  in
                          FStar_SMTEncoding_Term.unboxInt uu____4168  in
                        (uu____4165, uu____4167)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____4227 =
                          let uu____4228 = mk_args ts  in op uu____4228  in
                        FStar_All.pipe_right uu____4227 resBox  in
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
                        let uu____4360 =
                          let uu____4365 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4365  in
                        let uu____4374 =
                          let uu____4379 =
                            let uu____4381 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4381  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4379  in
                        mk_bv uu____4360 unary uu____4374 arg_tms2  in
                      let to_int =
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
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____4621 =
                        let uu____4631 =
                          FStar_List.tryFind
                            (fun uu____4655  ->
                               match uu____4655 with
                               | (l,uu____4666) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4631 FStar_Util.must  in
                      (match uu____4621 with
                       | (uu____4712,op) ->
                           let uu____4724 = op arg_tms1  in
                           (uu____4724, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___609_4734 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___609_4734.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___609_4734.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___609_4734.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___609_4734.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___609_4734.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___609_4734.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___609_4734.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___609_4734.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___609_4734.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___609_4734.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4736 = encode_term t env1  in
      match uu____4736 with
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
               (uu____4762,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4763;
                             FStar_SMTEncoding_Term.freevars = uu____4764;
                             FStar_SMTEncoding_Term.rng = uu____4765;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4766;
                  FStar_SMTEncoding_Term.freevars = uu____4767;
                  FStar_SMTEncoding_Term.rng = uu____4768;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4814 ->
               let uu____4815 = encode_formula t env1  in
               (match uu____4815 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4835 =
                            let uu____4840 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4840, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4835
                      | uu____4841 ->
                          let uu____4842 =
                            let uu____4853 =
                              let uu____4854 =
                                let uu____4859 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4859, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4854  in
                            ([[valid_tm]], vars, uu____4853)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4842
                       in
                    let ax =
                      let uu____4869 =
                        let uu____4877 =
                          let uu____4879 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4879  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4877)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4869  in
                    let uu____4885 =
                      let uu____4886 =
                        let uu____4889 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4889  in
                      FStar_List.append decls uu____4886  in
                    (tm, uu____4885)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let t0 = t1  in
      (let uu____4902 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4902
       then
         let uu____4907 = FStar_Syntax_Print.tag_of_term t1  in
         let uu____4909 = FStar_Syntax_Print.term_to_string t1  in
         FStar_Util.print2 "(%s)   %s\n" uu____4907 uu____4909
       else ());
      (match t1.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4918 ->
           let uu____4933 =
             let uu____4935 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4938 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4940 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4935
               uu____4938 uu____4940
              in
           failwith uu____4933
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4947 =
             let uu____4949 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4952 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4954 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4949
               uu____4952 uu____4954
              in
           failwith uu____4947
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4964 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4964
             then
               let uu____4969 = FStar_Syntax_Print.term_to_string t1  in
               let uu____4971 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4969
                 uu____4971
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4977 =
             let uu____4979 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4979
              in
           failwith uu____4977
       | FStar_Syntax_Syntax.Tm_ascribed (t2,(k,uu____4988),uu____4989) ->
           let uu____5038 =
             match k with
             | FStar_Util.Inl t3 -> FStar_Syntax_Util.is_unit t3
             | uu____5048 -> false  in
           if uu____5038
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t2 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____5066) ->
           let tv =
             let uu____5072 =
               let uu____5079 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____5079
                in
             uu____5072 t1.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____5083 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____5083
             then
               let uu____5088 = FStar_Syntax_Print.term_to_string t0  in
               let uu____5090 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____5088
                 uu____5090
             else ());
            (let t2 =
               let uu____5098 =
                 let uu____5109 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____5109]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____5098
                in
             encode_term t2 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t2,FStar_Syntax_Syntax.Meta_pattern uu____5135) ->
           encode_term t2
             (let uu___682_5161 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___682_5161.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___682_5161.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___682_5161.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___682_5161.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___682_5161.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___682_5161.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___682_5161.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___682_5161.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___682_5161.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___682_5161.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t2,uu____5164) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t2 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t2, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let encode_freev uu____5181 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v.FStar_Syntax_Syntax.fv_name
                in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v.FStar_Syntax_Syntax.fv_name
                in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
             let uu____5186 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu____5210 ->
                     let sym_name =
                       let uu____5221 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5221  in
                     let uu____5224 =
                       let uu____5227 =
                         let uu____5228 =
                           let uu____5236 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5236,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5228  in
                       [uu____5227]  in
                     (uu____5224, sym_name)
                 | FStar_SMTEncoding_Term.App (uu____5243,[]) ->
                     let sym_name =
                       let uu____5248 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5248  in
                     let uu____5251 =
                       let uu____5254 =
                         let uu____5255 =
                           let uu____5263 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5263,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5255  in
                       [uu____5254]  in
                     (uu____5251, sym_name)
                 | uu____5270 -> ([], "")
               else ([], "")  in
             match uu____5186 with
             | (aux_decls,sym_name) ->
                 let uu____5293 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls []
                    in
                 (tok, uu____5293)
              in
           let uu____5301 = head_redex env t1  in
           if uu____5301
           then
             let uu____5308 = maybe_whnf env t1  in
             (match uu____5308 with
              | FStar_Pervasives_Native.None  -> encode_freev ()
              | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu____5318 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5320) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5350 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5350 with
            | (binders1,res) ->
                let uu____5361 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5361
                then
                  let uu____5368 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5368 with
                   | (vars,guards_l,env',decls,uu____5393) ->
                       let fsym =
                         let uu____5407 =
                           let uu____5413 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5413, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5407  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5419 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___741_5428 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___741_5428.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___741_5428.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___741_5428.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___741_5428.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___741_5428.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___741_5428.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___741_5428.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___741_5428.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___741_5428.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___741_5428.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___741_5428.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___741_5428.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___741_5428.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___741_5428.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___741_5428.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___741_5428.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___741_5428.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___741_5428.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___741_5428.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___741_5428.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___741_5428.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___741_5428.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___741_5428.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___741_5428.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___741_5428.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___741_5428.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___741_5428.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___741_5428.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___741_5428.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___741_5428.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___741_5428.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___741_5428.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___741_5428.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___741_5428.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___741_5428.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___741_5428.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___741_5428.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___741_5428.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___741_5428.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___741_5428.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___741_5428.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___741_5428.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___741_5428.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___741_5428.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___741_5428.FStar_TypeChecker_Env.erasable_types_tab)
                            }) res
                          in
                       (match uu____5419 with
                        | (pre_opt,res_t) ->
                            let uu____5440 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5440 with
                             | (res_pred,decls') ->
                                 let uu____5451 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5464 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5464, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5468 =
                                         encode_formula pre env'  in
                                       (match uu____5468 with
                                        | (guard,decls0) ->
                                            let uu____5481 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5481, decls0))
                                    in
                                 (match uu____5451 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        let uu____5496 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv)
                                           in
                                        FStar_All.pipe_right uu____5496
                                          FStar_Syntax_Util.is_pure_comp
                                         in
                                      let t_interp =
                                        let uu____5505 =
                                          let uu____5516 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5516)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          uu____5505
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
                                        let uu____5538 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5538
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5557 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5559 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5557 <> uu____5559))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1)
                                         in
                                      let prefix =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_"  in
                                      let tkey_hash =
                                        let uu____5587 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix uu____5587  in
                                      let tsym =
                                        let uu____5591 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix uu____5591  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5605 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5605
                                        then
                                          let uu____5608 =
                                            let uu____5610 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5610 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5608
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t2 =
                                        let uu____5623 =
                                          let uu____5631 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5631)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5623
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5650 =
                                          let uu____5658 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5658,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5650
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
                                        let uu____5675 =
                                          let uu____5683 =
                                            let uu____5684 =
                                              let uu____5695 =
                                                let uu____5696 =
                                                  let uu____5701 =
                                                    let uu____5702 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5702
                                                     in
                                                  (f_has_t, uu____5701)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5696
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5695)
                                               in
                                            let uu____5720 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5720 uu____5684  in
                                          (uu____5683,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5675
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5743 =
                                          let uu____5751 =
                                            let uu____5752 =
                                              let uu____5763 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5763)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5752
                                             in
                                          (uu____5751,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5743
                                         in
                                      let t_decls =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5786 =
                                        let uu____5787 =
                                          let uu____5790 =
                                            let uu____5793 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5793
                                             in
                                          FStar_List.append decls' uu____5790
                                           in
                                        FStar_List.append decls uu____5787
                                         in
                                      (t2, uu____5786)))))
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
                     let uu____5814 =
                       let uu____5822 =
                         FStar_SMTEncoding_Term.mk_HasType t2
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5822,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5814  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t2  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5835 =
                       let uu____5843 =
                         let uu____5844 =
                           let uu____5855 =
                             let uu____5856 =
                               let uu____5861 =
                                 let uu____5862 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5862
                                  in
                               (f_has_t, uu____5861)  in
                             FStar_SMTEncoding_Util.mkImp uu____5856  in
                           ([[f_has_t]], [fsym], uu____5855)  in
                         let uu____5888 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5888 uu____5844  in
                       (uu____5843, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5835  in
                   let uu____5905 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t2, uu____5905)))
       | FStar_Syntax_Syntax.Tm_refine uu____5908 ->
           let uu____5915 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5925 =
               normalize_refinement steps env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5925 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5934;
                 FStar_Syntax_Syntax.vars = uu____5935;_} ->
                 let uu____5942 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5942 with
                  | (b,f1) ->
                      let uu____5969 =
                        let uu____5970 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5970  in
                      (uu____5969, f1))
             | uu____5987 -> failwith "impossible"  in
           (match uu____5915 with
            | (x,f) ->
                let uu____6005 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6005 with
                 | (base_t,decls) ->
                     let uu____6016 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____6016 with
                      | (x1,xtm,env') ->
                          let uu____6033 = encode_formula f env'  in
                          (match uu____6033 with
                           | (refinement,decls') ->
                               let uu____6044 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6044 with
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
                                      let uu____6072 =
                                        let uu____6083 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6094 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6083
                                          uu____6094
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6072
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____6148 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____6148 <> x1) &&
                                                (let uu____6152 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____6152 <> fsym)))
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
                                    ((let uu____6185 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____6185
                                      then
                                        let uu____6189 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____6191 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6189 tkey_hash uu____6191
                                      else ());
                                     (let tsym =
                                        let uu____6198 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____6198
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
                                        let uu____6218 =
                                          let uu____6226 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____6226)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6218
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
                                      let t_haseq =
                                        let uu____6246 =
                                          let uu____6254 =
                                            let uu____6255 =
                                              let uu____6266 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6266)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6255
                                             in
                                          (uu____6254,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6246
                                         in
                                      let t_kinding =
                                        let uu____6280 =
                                          let uu____6288 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6288,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6280
                                         in
                                      let t_interp =
                                        let uu____6302 =
                                          let uu____6310 =
                                            let uu____6311 =
                                              let uu____6322 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6322)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6311
                                             in
                                          (uu____6310,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6302
                                         in
                                      let t_decls =
                                        [tdecl; t_kinding; t_interp; t_haseq]
                                         in
                                      let uu____6354 =
                                        let uu____6355 =
                                          let uu____6358 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6358
                                           in
                                        FStar_List.append decls uu____6355
                                         in
                                      (t2, uu____6354))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6362) ->
           let ttm =
             let uu____6380 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6380  in
           let uu____6382 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6382 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6394 =
                    let uu____6402 =
                      let uu____6404 =
                        let uu____6406 =
                          let uu____6408 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6408  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6406  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6404
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6402)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6394  in
                let uu____6414 =
                  let uu____6415 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6415  in
                (ttm, uu____6414))
       | FStar_Syntax_Syntax.Tm_app uu____6422 ->
           let uu____6439 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6439 with
            | (head,args_e) ->
                let uu____6486 =
                  let uu____6503 = head_redex env head  in
                  if uu____6503
                  then
                    let uu____6522 = maybe_whnf env t0  in
                    match uu____6522 with
                    | FStar_Pervasives_Native.None  -> (head, args_e)
                    | FStar_Pervasives_Native.Some t2 ->
                        FStar_Syntax_Util.head_and_args t2
                  else (head, args_e)  in
                (match uu____6486 with
                 | (head1,args_e1) ->
                     let uu____6598 =
                       let uu____6613 =
                         let uu____6614 = FStar_Syntax_Subst.compress head1
                            in
                         uu____6614.FStar_Syntax_Syntax.n  in
                       (uu____6613, args_e1)  in
                     (match uu____6598 with
                      | uu____6631 when is_arithmetic_primitive head1 args_e1
                          -> encode_arith_term env head1 args_e1
                      | uu____6654 when is_BitVector_primitive head1 args_e1
                          -> encode_BitVector_term env head1 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6672) when
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
                            FStar_Syntax_Syntax.pos = uu____6694;
                            FStar_Syntax_Syntax.vars = uu____6695;_},uu____6696),uu____6697)
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
                            FStar_Syntax_Syntax.pos = uu____6723;
                            FStar_Syntax_Syntax.vars = uu____6724;_},uu____6725),
                         (v0,uu____6727)::(v1,uu____6729)::(v2,uu____6731)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6802 = encode_term v0 env  in
                          (match uu____6802 with
                           | (v01,decls0) ->
                               let uu____6813 = encode_term v1 env  in
                               (match uu____6813 with
                                | (v11,decls1) ->
                                    let uu____6824 = encode_term v2 env  in
                                    (match uu____6824 with
                                     | (v21,decls2) ->
                                         let uu____6835 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6835,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_fvar
                         fv,(v0,uu____6838)::(v1,uu____6840)::(v2,uu____6842)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6909 = encode_term v0 env  in
                          (match uu____6909 with
                           | (v01,decls0) ->
                               let uu____6920 = encode_term v1 env  in
                               (match uu____6920 with
                                | (v11,decls1) ->
                                    let uu____6931 = encode_term v2 env  in
                                    (match uu____6931 with
                                     | (v21,decls2) ->
                                         let uu____6942 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6942,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of ),(arg,uu____6944)::[])
                          ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of
                         ),(arg,uu____6980)::(rng,uu____6982)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify ),uu____7033) ->
                          let e0 =
                            let uu____7055 = FStar_List.hd args_e1  in
                            FStar_TypeChecker_Util.reify_body_with_arg
                              env.FStar_SMTEncoding_Env.tcenv [] head1
                              uu____7055
                             in
                          ((let uu____7065 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify")
                               in
                            if uu____7065
                            then
                              let uu____7070 =
                                FStar_Syntax_Print.term_to_string e0  in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu____7070
                            else ());
                           (let e =
                              let uu____7078 =
                                let uu____7083 =
                                  FStar_TypeChecker_Util.remove_reify e0  in
                                let uu____7084 = FStar_List.tl args_e1  in
                                FStar_Syntax_Syntax.mk_Tm_app uu____7083
                                  uu____7084
                                 in
                              uu____7078 FStar_Pervasives_Native.None
                                t0.FStar_Syntax_Syntax.pos
                               in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect
                         uu____7093),(arg,uu____7095)::[]) ->
                          encode_term arg env
                      | uu____7130 ->
                          let uu____7145 = encode_args args_e1 env  in
                          (match uu____7145 with
                           | (args,decls) ->
                               let encode_partial_app ht_opt =
                                 let uu____7214 = encode_term head1 env  in
                                 match uu____7214 with
                                 | (smt_head,decls') ->
                                     let app_tm = mk_Apply_args smt_head args
                                        in
                                     (match ht_opt with
                                      | uu____7234 when
                                          Prims.int_one = Prims.int_one ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type,formals,c) ->
                                          ((let uu____7306 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp")
                                               in
                                            if uu____7306
                                            then
                                              let uu____7310 =
                                                FStar_Syntax_Print.term_to_string
                                                  head1
                                                 in
                                              let uu____7312 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type
                                                 in
                                              let uu____7314 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals
                                                 in
                                              let uu____7317 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c
                                                 in
                                              let uu____7319 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1
                                                 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu____7310 uu____7312
                                                uu____7314 uu____7317
                                                uu____7319
                                            else ());
                                           (let uu____7324 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals
                                               in
                                            match uu____7324 with
                                            | (formals1,rest) ->
                                                let subst =
                                                  FStar_List.map2
                                                    (fun uu____7422  ->
                                                       fun uu____7423  ->
                                                         match (uu____7422,
                                                                 uu____7423)
                                                         with
                                                         | ((bv,uu____7453),
                                                            (a,uu____7455))
                                                             ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1
                                                   in
                                                let ty =
                                                  let uu____7487 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7487
                                                    (FStar_Syntax_Subst.subst
                                                       subst)
                                                   in
                                                ((let uu____7491 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp")
                                                     in
                                                  if uu____7491
                                                  then
                                                    let uu____7495 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty
                                                       in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu____7495
                                                  else ());
                                                 (let uu____7500 =
                                                    let uu____7513 =
                                                      FStar_List.fold_left2
                                                        (fun uu____7548  ->
                                                           fun uu____7549  ->
                                                             fun e  ->
                                                               match 
                                                                 (uu____7548,
                                                                   uu____7549)
                                                               with
                                                               | ((t_hyps,decls1),
                                                                  (bv,uu____7590))
                                                                   ->
                                                                   let t2 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                   let uu____7618
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t2 env e
                                                                     in
                                                                   (match uu____7618
                                                                    with
                                                                    | 
                                                                    (t_hyp,decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu____7634
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7634
                                                                    then
                                                                    let uu____7638
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____7640
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7638
                                                                    uu____7640
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
                                                    match uu____7513 with
                                                    | (t_hyps,decls1) ->
                                                        let uu____7675 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu____7684 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu____7693 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                [])
                                                           in
                                                        (match uu____7675
                                                         with
                                                         | (t_head_hyp,decls'1)
                                                             ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7709 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm
                                                                in
                                                             (match uu____7709
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
                                                                  let uu____7731
                                                                    =
                                                                    let uu____7738
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars
                                                                     in
                                                                    if
                                                                    uu____7738
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu____7751
                                                                    =
                                                                    let uu____7753
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7753
                                                                     in
                                                                    if
                                                                    uu____7751
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu____7766
                                                                    =
                                                                    let uu____7772
                                                                    =
                                                                    let uu____7774
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7774
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7772)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7766);
                                                                    ([],
                                                                    cvars)))
                                                                     in
                                                                  (match uu____7731
                                                                   with
                                                                   | 
                                                                   (pattern1,vars)
                                                                    ->
                                                                    (vars,
                                                                    pattern1,
                                                                    has_type,
                                                                    (FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls''))))))
                                                     in
                                                  match uu____7500 with
                                                  | (vars,pattern1,has_type,decls'')
                                                      ->
                                                      ((let uu____7821 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp")
                                                           in
                                                        if uu____7821
                                                        then
                                                          let uu____7825 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type
                                                             in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu____7825
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm
                                                           in
                                                        let e_typing =
                                                          let uu____7833 =
                                                            let uu____7841 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern1],
                                                                  vars,
                                                                  has_type)
                                                               in
                                                            let uu____7850 =
                                                              let uu____7852
                                                                =
                                                                let uu____7854
                                                                  =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm
                                                                   in
                                                                FStar_Util.digest_of_string
                                                                  uu____7854
                                                                 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu____7852
                                                               in
                                                            (uu____7841,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu____7850)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7833
                                                           in
                                                        let uu____7860 =
                                                          let uu____7863 =
                                                            let uu____7866 =
                                                              let uu____7869
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
                                                                uu____7869
                                                               in
                                                            FStar_List.append
                                                              decls'
                                                              uu____7866
                                                             in
                                                          FStar_List.append
                                                            decls uu____7863
                                                           in
                                                        (app_tm, uu____7860)))))))
                                      | FStar_Pervasives_Native.None  ->
                                          failwith "impossible")
                                  in
                               let encode_full_app fv =
                                 let uu____7914 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv
                                    in
                                 match uu____7914 with
                                 | (fname,fuel_args,arity) ->
                                     let tm =
                                       maybe_curry_app
                                         t0.FStar_Syntax_Syntax.pos fname
                                         arity
                                         (FStar_List.append fuel_args args)
                                        in
                                     (tm, decls)
                                  in
                               let head2 = FStar_Syntax_Subst.compress head1
                                  in
                               let head_type =
                                 match head2.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_uinst
                                     ({
                                        FStar_Syntax_Syntax.n =
                                          FStar_Syntax_Syntax.Tm_name x;
                                        FStar_Syntax_Syntax.pos = uu____7957;
                                        FStar_Syntax_Syntax.vars = uu____7958;_},uu____7959)
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
                                        FStar_Syntax_Syntax.pos = uu____7966;
                                        FStar_Syntax_Syntax.vars = uu____7967;_},uu____7968)
                                     ->
                                     let uu____7973 =
                                       let uu____7974 =
                                         let uu____7979 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                            in
                                         FStar_All.pipe_right uu____7979
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7974
                                         FStar_Pervasives_Native.snd
                                        in
                                     FStar_Pervasives_Native.Some uu____7973
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu____8009 =
                                       let uu____8010 =
                                         let uu____8015 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                            in
                                         FStar_All.pipe_right uu____8015
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____8010
                                         FStar_Pervasives_Native.snd
                                        in
                                     FStar_Pervasives_Native.Some uu____8009
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____8044,(FStar_Util.Inl
                                                  t2,uu____8046),uu____8047)
                                     -> FStar_Pervasives_Native.Some t2
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____8094,(FStar_Util.Inr
                                                  c,uu____8096),uu____8097)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu____8144 -> FStar_Pervasives_Native.None
                                  in
                               (match head_type with
                                | FStar_Pervasives_Native.None  ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu____8168 =
                                      let head_type2 =
                                        let uu____8190 =
                                          normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1
                                           in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine
                                          uu____8190
                                         in
                                      let uu____8193 =
                                        curried_arrow_formals_comp head_type2
                                         in
                                      match uu____8193 with
                                      | (formals,c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu____8244 =
                                                normalize_refinement
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
                                                uu____8244
                                               in
                                            let uu____8245 =
                                              curried_arrow_formals_comp
                                                head_type3
                                               in
                                            (match uu____8245 with
                                             | (formals1,c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c)
                                       in
                                    (match uu____8168 with
                                     | (head_type2,formals,c) ->
                                         ((let uu____8328 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp")
                                              in
                                           if uu____8328
                                           then
                                             let uu____8332 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2
                                                in
                                             let uu____8334 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals
                                                in
                                             let uu____8337 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1
                                                in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu____8332 uu____8334
                                               uu____8337
                                           else ());
                                          (match head2.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8347;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8348;_},uu____8349)
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
                                           | uu____8367 ->
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
           let uu____8456 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8456 with
            | (bs1,body1,opening) ->
                let fallback uu____8479 =
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
                  let uu____8489 =
                    let uu____8490 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8490
                     in
                  let uu____8492 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8489, uu____8492)  in
                let is_impure rc =
                  let uu____8502 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8502 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8517 =
                          let uu____8530 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8530
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8517 with
                         | (t2,uu____8533,uu____8534) -> t2)
                    | FStar_Pervasives_Native.Some t2 -> t2  in
                  let uu____8552 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8552
                  then
                    let uu____8557 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8557
                  else
                    (let uu____8560 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8560
                     then
                       let uu____8565 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8565
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8573 =
                         let uu____8579 =
                           let uu____8581 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8581
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8579)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8573);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8586 =
                       (is_impure rc) &&
                         (let uu____8589 =
                            FStar_SMTEncoding_Util.is_smt_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8589)
                        in
                     if uu____8586
                     then fallback ()
                     else
                       (let uu____8598 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8598 with
                        | (vars,guards,envbody,decls,uu____8623) ->
                            let body2 =
                              let uu____8637 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8637
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv [] body1
                              else body1  in
                            let uu____8642 = encode_term body2 envbody  in
                            (match uu____8642 with
                             | (body3,decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect
                                    in
                                 let uu____8655 =
                                   let uu____8664 = codomain_eff rc  in
                                   match uu____8664 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8683 = encode_term tfun env
                                          in
                                       (match uu____8683 with
                                        | (t2,decls1) ->
                                            ((FStar_Pervasives_Native.Some t2),
                                              decls1))
                                    in
                                 (match uu____8655 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8717 =
                                          let uu____8728 =
                                            let uu____8729 =
                                              let uu____8734 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8734, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8729
                                             in
                                          ([], vars, uu____8728)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8717
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8742 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t2 ->
                                            let uu____8758 =
                                              let uu____8761 =
                                                let uu____8772 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t2
                                                   in
                                                FStar_List.append uu____8772
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8761
                                               in
                                            let uu____8799 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t2)
                                               in
                                            (uu____8758, uu____8799)
                                         in
                                      (match uu____8742 with
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
                                           ((let uu____8822 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8822
                                             then
                                               let uu____8827 =
                                                 let uu____8829 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8829
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8839 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8827 uu____8839
                                             else ());
                                            (let uu____8844 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8844 with
                                             | FStar_Pervasives_Native.Some
                                                 t2 ->
                                                 ((let uu____8853 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8853
                                                   then
                                                     let uu____8858 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t2
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8858
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
                                                   let uu____8871 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8871
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8880 =
                                                     let uu____8888 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8888)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8880
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8902 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8910
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue))
                                                              in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8902
                                                             is_pure
                                                            in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8911 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax)
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym
                                                          in
                                                       let uu____8925 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                          in
                                                       [uu____8925]
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
                                                       let uu____8933 =
                                                         let uu____8934 =
                                                           let uu____8942 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8942,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8934
                                                          in
                                                       [uu____8933]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8957 =
                                                     let uu____8965 =
                                                       let uu____8966 =
                                                         let uu____8977 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8977)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8966
                                                        in
                                                     (uu____8965,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8957
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8991 =
                                                   let uu____8992 =
                                                     let uu____8995 =
                                                       let uu____8998 =
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
                                                         decls'' uu____8998
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8995
                                                      in
                                                   FStar_List.append decls
                                                     uu____8992
                                                    in
                                                 (f, uu____8991)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____9001,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____9002;
                          FStar_Syntax_Syntax.lbunivs = uu____9003;
                          FStar_Syntax_Syntax.lbtyp = uu____9004;
                          FStar_Syntax_Syntax.lbeff = uu____9005;
                          FStar_Syntax_Syntax.lbdef = uu____9006;
                          FStar_Syntax_Syntax.lbattrs = uu____9007;
                          FStar_Syntax_Syntax.lbpos = uu____9008;_}::uu____9009),uu____9010)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____9044;
                FStar_Syntax_Syntax.lbtyp = t11;
                FStar_Syntax_Syntax.lbeff = uu____9046;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____9048;
                FStar_Syntax_Syntax.lbpos = uu____9049;_}::[]),e2)
           -> encode_let x t11 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false ,uu____9076::uu____9077),uu____9078) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____9101,lbs),uu____9103) ->
           let names =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb  ->
                     let uu____9156 = lb  in
                     match uu____9156 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____9163;
                         FStar_Syntax_Syntax.lbtyp = uu____9164;
                         FStar_Syntax_Syntax.lbeff = uu____9165;
                         FStar_Syntax_Syntax.lbdef = uu____9166;
                         FStar_Syntax_Syntax.lbattrs = uu____9167;
                         FStar_Syntax_Syntax.lbpos = uu____9168;_} ->
                         let x = FStar_Util.left lbname  in
                         let uu____9184 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname
                            in
                         let uu____9186 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         (uu____9184, uu____9186)))
              in
           FStar_Exn.raise (FStar_SMTEncoding_Env.Inner_let_rec names)
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
              let uu____9244 =
                let uu____9249 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9249 env  in
              match uu____9244 with
              | (ee1,decls1) ->
                  let uu____9274 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9274 with
                   | (xs,e21) ->
                       let uu____9299 = FStar_List.hd xs  in
                       (match uu____9299 with
                        | (x1,uu____9317) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____9323 = encode_body e21 env'  in
                            (match uu____9323 with
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
            let uu____9353 =
              let uu____9361 =
                let uu____9362 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9362  in
              FStar_SMTEncoding_Env.gen_term_var env uu____9361  in
            match uu____9353 with
            | (scrsym,scr',env1) ->
                let uu____9372 = encode_term e env1  in
                (match uu____9372 with
                 | (scr,decls) ->
                     let uu____9383 =
                       let encode_branch b uu____9412 =
                         match uu____9412 with
                         | (else_case,decls1) ->
                             let uu____9431 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9431 with
                              | (p,w,br) ->
                                  let uu____9457 = encode_pat env1 p  in
                                  (match uu____9457 with
                                   | (env0,pattern1) ->
                                       let guard = pattern1.guard scr'  in
                                       let projections =
                                         pattern1.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9494  ->
                                                   match uu____9494 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9501 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9523 =
                                               encode_term w1 env2  in
                                             (match uu____9523 with
                                              | (w2,decls2) ->
                                                  let uu____9536 =
                                                    let uu____9537 =
                                                      let uu____9542 =
                                                        let uu____9543 =
                                                          let uu____9548 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9548)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9543
                                                         in
                                                      (guard, uu____9542)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9537
                                                     in
                                                  (uu____9536, decls2))
                                          in
                                       (match uu____9501 with
                                        | (guard1,decls2) ->
                                            let uu____9563 =
                                              encode_br br env2  in
                                            (match uu____9563 with
                                             | (br1,decls3) ->
                                                 let uu____9576 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9576,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9383 with
                      | (match_tm,decls1) ->
                          let uu____9597 =
                            let uu____9598 =
                              let uu____9609 =
                                let uu____9616 =
                                  let uu____9621 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9621, scr)  in
                                [uu____9616]  in
                              (uu____9609, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9598
                              FStar_Range.dummyRange
                             in
                          (uu____9597, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9644 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9644
       then
         let uu____9647 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9647
       else ());
      (let uu____9652 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9652 with
       | (vars,pat_term) ->
           let uu____9669 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9711  ->
                     fun v  ->
                       match uu____9711 with
                       | (env1,vars1) ->
                           let uu____9747 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v  in
                           (match uu____9747 with
                            | (xx,uu____9766,env2) ->
                                let uu____9770 =
                                  let uu____9777 =
                                    let uu____9782 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v, uu____9782)  in
                                  uu____9777 :: vars1  in
                                (env2, uu____9770))) (env, []))
              in
           (match uu____9669 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9837 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9838 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9839 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9847 = encode_const c env1  in
                      (match uu____9847 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9855::uu____9856 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9860 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9883 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9883 with
                        | (uu____9891,uu____9892::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9897 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9933  ->
                                  match uu____9933 with
                                  | (arg,uu____9943) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9952 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9952))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9984) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____10015 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____10040 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____10086  ->
                                  match uu____10086 with
                                  | (arg,uu____10102) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10111 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10111))
                         in
                      FStar_All.pipe_right uu____10040 FStar_List.flatten
                   in
                let pat_term1 uu____10142 = encode_term pat_term env1  in
                let pattern1 =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern1)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun l  ->
    fun env  ->
      let uu____10152 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10200  ->
                fun uu____10201  ->
                  match (uu____10200, uu____10201) with
                  | ((tms,decls),(t,uu____10241)) ->
                      let uu____10268 = encode_term t env  in
                      (match uu____10268 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10152 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10346  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1417_10355 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1417_10355.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1417_10355.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1417_10355.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1417_10355.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1417_10355.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1417_10355.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1417_10355.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1417_10355.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1417_10355.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1417_10355.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1422_10372 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1422_10372.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1422_10372.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1422_10372.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1422_10372.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1422_10372.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1422_10372.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1422_10372.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1422_10372.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1422_10372.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1422_10372.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____10388 = FStar_Syntax_Util.head_and_args t  in
        match uu____10388 with
        | (head,args) ->
            let head1 = FStar_Syntax_Util.un_uinst head  in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10451::(x,uu____10453)::(t1,uu____10455)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10522 = encode_term x env1  in
                 (match uu____10522 with
                  | (x1,decls) ->
                      let uu____10533 = encode_term t1 env1  in
                      (match uu____10533 with
                       | (t2,decls') ->
                           let uu____10544 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10544, (FStar_List.append decls decls'))))
             | uu____10545 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10588  ->
             match uu____10588 with
             | (pats_l1,decls) ->
                 let uu____10633 =
                   FStar_List.fold_right
                     (fun uu____10668  ->
                        fun uu____10669  ->
                          match (uu____10668, uu____10669) with
                          | ((p,uu____10711),(pats1,decls1)) ->
                              let uu____10746 = encode_smt_pattern p  in
                              (match uu____10746 with
                               | (t,d) ->
                                   let uu____10761 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10761 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10778 =
                                            let uu____10784 =
                                              let uu____10786 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10788 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10786 uu____10788
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10784)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10778);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10633 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun phi  ->
    fun env  ->
      let debug phi1 =
        let uu____10848 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10848
        then
          let uu____10853 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10855 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10853 uu____10855
        else ()  in
      let enc f r l =
        let uu____10897 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10929 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10929 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10897 with
        | (decls,args) ->
            let uu____10960 =
              let uu___1486_10961 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1486_10961.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1486_10961.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10960, decls)
         in
      let const_op f r uu____10996 =
        let uu____11009 = f r  in (uu____11009, [])  in
      let un_op f l =
        let uu____11032 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11032  in
      let bin_op f uu___2_11052 =
        match uu___2_11052 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11063 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11104 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11129  ->
                 match uu____11129 with
                 | (t,uu____11145) ->
                     let uu____11150 = encode_formula t env  in
                     (match uu____11150 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11104 with
        | (decls,phis) ->
            let uu____11179 =
              let uu___1516_11180 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1516_11180.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1516_11180.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11179, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11243  ->
               match uu____11243 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11264) -> false
                    | uu____11267 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu____11286 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11286
        else
          (let uu____11303 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11303 r rf)
         in
      let eq3_op r args =
        let n = FStar_List.length args  in
        if n = (Prims.of_int (4))
        then
          let uu____11371 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11403 =
                       let uu____11408 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11409 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11408, uu____11409)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11403
                 | uu____11410 -> failwith "Impossible")
             in
          uu____11371 r args
        else
          (let uu____11416 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n)
              in
           failwith uu____11416)
         in
      let h_equals_op r args =
        let n = FStar_List.length args  in
        if n = (Prims.of_int (4))
        then
          let uu____11478 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11510 =
                       let uu____11515 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11516 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11515, uu____11516)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11510
                 | uu____11517 -> failwith "Impossible")
             in
          uu____11478 r args
        else
          (let uu____11523 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n)
              in
           failwith uu____11523)
         in
      let mk_imp r uu___3_11552 =
        match uu___3_11552 with
        | (lhs,uu____11558)::(rhs,uu____11560)::[] ->
            let uu____11601 = encode_formula rhs env  in
            (match uu____11601 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11616) ->
                      (l1, decls1)
                  | uu____11621 ->
                      let uu____11622 = encode_formula lhs env  in
                      (match uu____11622 with
                       | (l2,decls2) ->
                           let uu____11633 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11633, (FStar_List.append decls1 decls2)))))
        | uu____11634 -> failwith "impossible"  in
      let mk_ite r uu___4_11662 =
        match uu___4_11662 with
        | (guard,uu____11668)::(_then,uu____11670)::(_else,uu____11672)::[]
            ->
            let uu____11729 = encode_formula guard env  in
            (match uu____11729 with
             | (g,decls1) ->
                 let uu____11740 = encode_formula _then env  in
                 (match uu____11740 with
                  | (t,decls2) ->
                      let uu____11751 = encode_formula _else env  in
                      (match uu____11751 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11763 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11793 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11793  in
      let connectives =
        let uu____11823 =
          let uu____11848 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11848)  in
        let uu____11891 =
          let uu____11918 =
            let uu____11943 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11943)  in
          let uu____11986 =
            let uu____12013 =
              let uu____12040 =
                let uu____12065 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____12065)  in
              let uu____12108 =
                let uu____12135 =
                  let uu____12162 =
                    let uu____12187 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12187)  in
                  [uu____12162;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12135  in
              uu____12040 :: uu____12108  in
            (FStar_Parser_Const.imp_lid, mk_imp) :: uu____12013  in
          uu____11918 :: uu____11986  in
        uu____11823 :: uu____11891  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12732 = encode_formula phi' env  in
            (match uu____12732 with
             | (phi2,decls) ->
                 let uu____12743 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12743, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12745 ->
            let uu____12752 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12752 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12791 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12791 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12803;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12805;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12807;
                 FStar_Syntax_Syntax.lbpos = uu____12808;_}::[]),e2)
            ->
            let uu____12835 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12835 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head1 = FStar_Syntax_Util.un_uinst head  in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12888::(x,uu____12890)::(t,uu____12892)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12959 = encode_term x env  in
                 (match uu____12959 with
                  | (x1,decls) ->
                      let uu____12970 = encode_term t env  in
                      (match uu____12970 with
                       | (t1,decls') ->
                           let uu____12981 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12981, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12984)::(msg,uu____12986)::(phi2,uu____12988)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____13055 =
                   let uu____13060 =
                     let uu____13061 = FStar_Syntax_Subst.compress r  in
                     uu____13061.FStar_Syntax_Syntax.n  in
                   let uu____13064 =
                     let uu____13065 = FStar_Syntax_Subst.compress msg  in
                     uu____13065.FStar_Syntax_Syntax.n  in
                   (uu____13060, uu____13064)  in
                 (match uu____13055 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____13074))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____13085 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____13092)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____13127 ->
                 let encode_valid uu____13151 =
                   let uu____13152 = encode_term phi1 env  in
                   match uu____13152 with
                   | (tt,decls) ->
                       let tt1 =
                         let uu____13164 =
                           let uu____13166 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng
                              in
                           let uu____13167 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos
                              in
                           FStar_Range.rng_included uu____13166 uu____13167
                            in
                         if uu____13164
                         then tt
                         else
                           (let uu___1704_13171 = tt  in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___1704_13171.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___1704_13171.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            })
                          in
                       let uu____13172 = FStar_SMTEncoding_Term.mk_Valid tt1
                          in
                       (uu____13172, decls)
                    in
                 let uu____13173 = head_redex env head1  in
                 if uu____13173
                 then
                   let uu____13180 = maybe_whnf env head1  in
                   (match uu____13180 with
                    | FStar_Pervasives_Native.None  -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu____13190 ->
            let uu____13191 = encode_term phi1 env  in
            (match uu____13191 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____13203 =
                     let uu____13205 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____13206 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____13205 uu____13206  in
                   if uu____13203
                   then tt
                   else
                     (let uu___1716_13210 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1716_13210.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1716_13210.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____13211 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____13211, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13255 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13255 with
        | (vars,guards,env2,decls,uu____13294) ->
            let uu____13307 = encode_smt_patterns ps env2  in
            (match uu____13307 with
             | (pats,decls') ->
                 let uu____13344 = encode_formula body env2  in
                 (match uu____13344 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13376;
                             FStar_SMTEncoding_Term.rng = uu____13377;_}::[])::[]
                            when
                            let uu____13397 =
                              FStar_Ident.string_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13397 = gf -> []
                        | uu____13400 -> guards  in
                      let uu____13405 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13405, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13416 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13416 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13425 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13531  ->
                     match uu____13531 with
                     | (l,uu____13556) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13425 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13625,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13717 = encode_q_body env vars pats body  in
             match uu____13717 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13762 =
                     let uu____13773 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13773)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13762
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13804 = encode_q_body env vars pats body  in
             match uu____13804 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13848 =
                   let uu____13849 =
                     let uu____13860 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13860)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13849
                    in
                 (uu____13848, decls))))
