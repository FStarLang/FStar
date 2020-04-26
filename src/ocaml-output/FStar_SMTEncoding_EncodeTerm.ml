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
          let uu____2478 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____2478, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____2480 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____2480, [])
      | FStar_Const.Const_char c1 ->
          let uu____2483 =
            let uu____2484 =
              let uu____2492 =
                let uu____2495 =
                  let uu____2496 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____2496  in
                [uu____2495]  in
              ("FStar.Char.__char_of_int", uu____2492)  in
            FStar_SMTEncoding_Util.mkApp uu____2484  in
          (uu____2483, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____2514 =
            let uu____2515 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____2515  in
          (uu____2514, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2536) ->
          let uu____2539 =
            let uu____2540 = FStar_SMTEncoding_Util.mk_String_const s  in
            FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2540
             in
          (uu____2539, [])
      | FStar_Const.Const_range uu____2541 ->
          let uu____2542 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2542, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2545 =
            let uu____2546 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2546  in
          (uu____2545, [])
      | c1 ->
          let uu____2548 =
            let uu____2550 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2550  in
          failwith uu____2548

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
        (let uu____2579 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2579
         then
           let uu____2582 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2582
         else ());
        (let uu____2588 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2670  ->
                   fun b  ->
                     match uu____2670 with
                     | (vars,guards,env1,decls,names) ->
                         let uu____2735 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2751 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2751 with
                           | (xxsym,xx,env') ->
                               let uu____2776 =
                                 let uu____2781 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2781 env1 xx
                                  in
                               (match uu____2776 with
                                | (guard_x_t,decls') ->
                                    let uu____2796 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2796, guard_x_t, env', decls', x))
                            in
                         (match uu____2735 with
                          | (v,g,env2,decls',n) ->
                              ((v :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], []))
            in
         match uu____2588 with
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
          let uu____2896 = encode_term t env  in
          match uu____2896 with
          | (t1,decls) ->
              let uu____2907 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2907, decls)

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
          let uu____2918 = encode_term t env  in
          match uu____2918 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2933 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2933, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2935 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2935, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head  ->
      fun args_e  ->
        let uu____2941 = encode_args args_e env  in
        match uu____2941 with
        | (arg_tms,decls) ->
            let head_fv =
              match head.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2960 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2982 = FStar_List.hd arg_tms1  in unbox uu____2982
               in
            let binary unbox arg_tms1 =
              let uu____3007 =
                let uu____3008 = FStar_List.hd arg_tms1  in unbox uu____3008
                 in
              let uu____3009 =
                let uu____3010 =
                  let uu____3011 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____3011  in
                unbox uu____3010  in
              (uu____3007, uu____3009)  in
            let mk_default uu____3019 =
              let uu____3020 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3020 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____3109 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____3109
              then
                let uu____3112 =
                  let uu____3113 = mk_args ts  in op uu____3113  in
                FStar_All.pipe_right uu____3112 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____3171 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3171
              then
                let uu____3174 = binary unbox ts  in
                match uu____3174 with
                | (t1,t2) ->
                    let uu____3181 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3181 box
              else
                (let uu____3187 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3187
                 then
                   let uu____3190 =
                     let uu____3191 = binary unbox ts  in op uu____3191  in
                   FStar_All.pipe_right uu____3190 box
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
            let uu____3626 =
              let uu____3636 =
                FStar_List.tryFind
                  (fun uu____3660  ->
                     match uu____3660 with
                     | (l,uu____3671) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3636 FStar_Util.must  in
            (match uu____3626 with
             | (uu____3715,op) ->
                 let uu____3727 = op arg_tms  in (uu____3727, decls))

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
        let uu____3743 = FStar_List.hd args_e  in
        match uu____3743 with
        | (tm_sz,uu____3759) ->
            let uu____3768 = uu____3743  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls []  in
            let uu____3779 =
              match ((head.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3805::(sz_arg,uu____3807)::uu____3808::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3875 =
                    let uu____3876 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3876  in
                  let uu____3903 =
                    let uu____3907 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3907  in
                  (uu____3875, uu____3903)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3914::(sz_arg,uu____3916)::uu____3917::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3984 =
                    let uu____3986 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3986
                     in
                  failwith uu____3984
              | uu____3996 ->
                  let uu____4011 = FStar_List.tail args_e  in
                  (uu____4011, FStar_Pervasives_Native.None)
               in
            (match uu____3779 with
             | (arg_tms,ext_sz) ->
                 let uu____4038 = encode_args arg_tms env  in
                 (match uu____4038 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____4059 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____4071 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____4071  in
                      let unary_arith arg_tms2 =
                        let uu____4082 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____4082  in
                      let binary arg_tms2 =
                        let uu____4097 =
                          let uu____4098 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4098
                           in
                        let uu____4099 =
                          let uu____4100 =
                            let uu____4101 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4101  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4100
                           in
                        (uu____4097, uu____4099)  in
                      let binary_arith arg_tms2 =
                        let uu____4118 =
                          let uu____4119 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4119
                           in
                        let uu____4120 =
                          let uu____4121 =
                            let uu____4122 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____4122  in
                          FStar_SMTEncoding_Term.unboxInt uu____4121  in
                        (uu____4118, uu____4120)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____4180 =
                          let uu____4181 = mk_args ts  in op uu____4181  in
                        FStar_All.pipe_right uu____4180 resBox  in
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
                        let uu____4313 =
                          let uu____4318 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____4318  in
                        let uu____4327 =
                          let uu____4332 =
                            let uu____4334 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____4334  in
                          FStar_SMTEncoding_Term.boxBitVec uu____4332  in
                        mk_bv uu____4313 unary uu____4327 arg_tms2  in
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
                      let uu____4574 =
                        let uu____4584 =
                          FStar_List.tryFind
                            (fun uu____4608  ->
                               match uu____4608 with
                               | (l,uu____4619) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4584 FStar_Util.must  in
                      (match uu____4574 with
                       | (uu____4665,op) ->
                           let uu____4677 = op arg_tms1  in
                           (uu____4677, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___601_4687 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___601_4687.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___601_4687.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___601_4687.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___601_4687.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___601_4687.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___601_4687.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___601_4687.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___601_4687.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___601_4687.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___601_4687.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4689 = encode_term t env1  in
      match uu____4689 with
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
               (uu____4715,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4716;
                             FStar_SMTEncoding_Term.freevars = uu____4717;
                             FStar_SMTEncoding_Term.rng = uu____4718;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4719;
                  FStar_SMTEncoding_Term.freevars = uu____4720;
                  FStar_SMTEncoding_Term.rng = uu____4721;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4767 ->
               let uu____4768 = encode_formula t env1  in
               (match uu____4768 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4788 =
                            let uu____4793 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4793, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4788
                      | uu____4794 ->
                          let uu____4795 =
                            let uu____4806 =
                              let uu____4807 =
                                let uu____4812 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4812, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4807  in
                            ([[valid_tm]], vars, uu____4806)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4795
                       in
                    let ax =
                      let uu____4822 =
                        let uu____4830 =
                          let uu____4832 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4832  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4830)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4822  in
                    let uu____4838 =
                      let uu____4839 =
                        let uu____4842 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4842  in
                      FStar_List.append decls uu____4839  in
                    (tm, uu____4838)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let t0 = t1  in
      (let uu____4855 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4855
       then
         let uu____4860 = FStar_Syntax_Print.tag_of_term t1  in
         let uu____4862 = FStar_Syntax_Print.term_to_string t1  in
         FStar_Util.print2 "(%s)   %s\n" uu____4860 uu____4862
       else ());
      (match t1.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4871 ->
           let uu____4886 =
             let uu____4888 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4891 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4893 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4888
               uu____4891 uu____4893
              in
           failwith uu____4886
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4900 =
             let uu____4902 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos
                in
             let uu____4905 = FStar_Syntax_Print.tag_of_term t1  in
             let uu____4907 = FStar_Syntax_Print.term_to_string t1  in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4902
               uu____4905 uu____4907
              in
           failwith uu____4900
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4917 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4917
             then
               let uu____4922 = FStar_Syntax_Print.term_to_string t1  in
               let uu____4924 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4922
                 uu____4924
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4930 =
             let uu____4932 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4932
              in
           failwith uu____4930
       | FStar_Syntax_Syntax.Tm_ascribed (t2,(k,uu____4941),uu____4942) ->
           let uu____4991 =
             match k with
             | FStar_Util.Inl t3 -> FStar_Syntax_Util.is_unit t3
             | uu____5001 -> false  in
           if uu____4991
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t2 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____5019) ->
           let tv =
             let uu____5025 =
               let uu____5032 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____5032
                in
             uu____5025 t1.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____5036 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____5036
             then
               let uu____5041 = FStar_Syntax_Print.term_to_string t0  in
               let uu____5043 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____5041
                 uu____5043
             else ());
            (let t2 =
               let uu____5051 =
                 let uu____5062 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____5062]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____5051
                in
             encode_term t2 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t2,FStar_Syntax_Syntax.Meta_pattern uu____5088) ->
           encode_term t2
             (let uu___674_5114 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___674_5114.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___674_5114.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___674_5114.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___674_5114.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___674_5114.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___674_5114.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___674_5114.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___674_5114.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___674_5114.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___674_5114.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t2,uu____5117) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t2 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t2, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let encode_freev uu____5134 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v.FStar_Syntax_Syntax.fv_name
                in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v.FStar_Syntax_Syntax.fv_name
                in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
             let uu____5139 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu____5163 ->
                     let sym_name =
                       let uu____5174 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5174  in
                     let uu____5177 =
                       let uu____5180 =
                         let uu____5181 =
                           let uu____5189 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5189,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5181  in
                       [uu____5180]  in
                     (uu____5177, sym_name)
                 | FStar_SMTEncoding_Term.App (uu____5196,[]) ->
                     let sym_name =
                       let uu____5201 = FStar_Util.digest_of_string tkey_hash
                          in
                       Prims.op_Hat "@kick_partial_app_" uu____5201  in
                     let uu____5204 =
                       let uu____5207 =
                         let uu____5208 =
                           let uu____5216 =
                             FStar_SMTEncoding_Term.kick_partial_app tok  in
                           (uu____5216,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name)
                            in
                         FStar_SMTEncoding_Util.mkAssume uu____5208  in
                       [uu____5207]  in
                     (uu____5204, sym_name)
                 | uu____5223 -> ([], "")
               else ([], "")  in
             match uu____5139 with
             | (aux_decls,sym_name) ->
                 let uu____5246 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls []
                    in
                 (tok, uu____5246)
              in
           let uu____5254 = head_redex env t1  in
           if uu____5254
           then
             let uu____5261 = maybe_whnf env t1  in
             (match uu____5261 with
              | FStar_Pervasives_Native.None  -> encode_freev ()
              | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu____5271 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5273) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____5303 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5303 with
            | (binders1,res) ->
                let uu____5314 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5314
                then
                  let uu____5321 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5321 with
                   | (vars,guards_l,env',decls,uu____5346) ->
                       let fsym =
                         let uu____5360 =
                           let uu____5366 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____5366, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____5360  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5372 =
                         FStar_Syntax_Unionfind.with_uf_enabled
                           (fun uu____5386  ->
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                (let uu___734_5389 =
                                   env.FStar_SMTEncoding_Env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___734_5389.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___734_5389.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___734_5389.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___734_5389.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___734_5389.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___734_5389.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___734_5389.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___734_5389.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___734_5389.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___734_5389.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___734_5389.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___734_5389.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___734_5389.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___734_5389.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___734_5389.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___734_5389.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___734_5389.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___734_5389.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___734_5389.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___734_5389.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___734_5389.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___734_5389.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___734_5389.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___734_5389.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___734_5389.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___734_5389.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___734_5389.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___734_5389.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___734_5389.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___734_5389.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___734_5389.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___734_5389.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___734_5389.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___734_5389.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___734_5389.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___734_5389.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___734_5389.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___734_5389.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___734_5389.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___734_5389.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___734_5389.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___734_5389.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___734_5389.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___734_5389.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___734_5389.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) res)
                          in
                       (match uu____5372 with
                        | (pre_opt,res_t) ->
                            let uu____5401 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5401 with
                             | (res_pred,decls') ->
                                 let uu____5412 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5425 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l
                                          in
                                       (uu____5425, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5429 =
                                         encode_formula pre env'  in
                                       (match uu____5429 with
                                        | (guard,decls0) ->
                                            let uu____5442 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l)
                                               in
                                            (uu____5442, decls0))
                                    in
                                 (match uu____5412 with
                                  | (guards,guard_decls) ->
                                      let is_pure =
                                        let uu____5457 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv)
                                           in
                                        FStar_All.pipe_right uu____5457
                                          FStar_Syntax_Util.is_pure_comp
                                         in
                                      let t_interp =
                                        let uu____5466 =
                                          let uu____5477 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred)
                                             in
                                          ([[app]], vars, uu____5477)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          uu____5466
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
                                        let uu____5499 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1
                                           in
                                        FStar_All.pipe_right uu____5499
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____5518 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____5520 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____5518 <> uu____5520))
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
                                        let uu____5548 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey
                                           in
                                        Prims.op_Hat prefix uu____5548  in
                                      let tsym =
                                        let uu____5552 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat prefix uu____5552  in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5566 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5566
                                        then
                                          let uu____5569 =
                                            let uu____5571 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5571 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5569
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t2 =
                                        let uu____5584 =
                                          let uu____5592 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5592)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5584
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5611 =
                                          let uu____5619 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5619,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5611
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
                                        let uu____5636 =
                                          let uu____5644 =
                                            let uu____5645 =
                                              let uu____5656 =
                                                let uu____5657 =
                                                  let uu____5662 =
                                                    let uu____5663 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5663
                                                     in
                                                  (f_has_t, uu____5662)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5657
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5656)
                                               in
                                            let uu____5681 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5681 uu____5645  in
                                          (uu____5644,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5636
                                         in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5704 =
                                          let uu____5712 =
                                            let uu____5713 =
                                              let uu____5724 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5724)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5713
                                             in
                                          (uu____5712,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5704
                                         in
                                      let t_decls =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2]  in
                                      let uu____5747 =
                                        let uu____5748 =
                                          let uu____5751 =
                                            let uu____5754 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5754
                                             in
                                          FStar_List.append decls' uu____5751
                                           in
                                        FStar_List.append decls uu____5748
                                         in
                                      (t2, uu____5747)))))
                else
                  (let tkey_hash =
                     let uu____5761 =
                       encode_binders FStar_Pervasives_Native.None binders1
                         env
                        in
                     match uu____5761 with
                     | (vars,guards_l,env_bs,uu____5782,uu____5783) ->
                         let c1 =
                           let uu____5799 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev
                               env.FStar_SMTEncoding_Env.tcenv res
                              in
                           FStar_All.pipe_right uu____5799
                             FStar_Syntax_Syntax.mk_Comp
                            in
                         let uu____5802 =
                           let uu____5807 =
                             FStar_All.pipe_right c1
                               FStar_Syntax_Util.comp_result
                              in
                           encode_term uu____5807 env_bs  in
                         (match uu____5802 with
                          | (ct,uu____5812) ->
                              let uu____5813 =
                                let uu____5820 =
                                  FStar_All.pipe_right c1
                                    FStar_Syntax_Util.comp_effect_args
                                   in
                                encode_args uu____5820 env_bs  in
                              (match uu____5813 with
                               | (effect_args,uu____5823) ->
                                   let tkey =
                                     let uu____5829 =
                                       let uu____5840 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           (FStar_List.append guards_l
                                              (FStar_List.append [ct]
                                                 effect_args))
                                          in
                                       ([], vars, uu____5840)  in
                                     FStar_SMTEncoding_Term.mkForall
                                       t1.FStar_Syntax_Syntax.pos uu____5829
                                      in
                                   let tkey_hash =
                                     let uu____5849 =
                                       let uu____5851 =
                                         FStar_SMTEncoding_Term.hash_of_term
                                           tkey
                                          in
                                       let uu____5853 =
                                         let uu____5855 =
                                           let uu____5857 =
                                             FStar_All.pipe_right c1
                                               FStar_Syntax_Util.comp_effect_name
                                              in
                                           FStar_All.pipe_right uu____5857
                                             FStar_Ident.string_of_lid
                                            in
                                         Prims.op_Hat "@Effect=" uu____5855
                                          in
                                       Prims.op_Hat uu____5851 uu____5853  in
                                     Prims.op_Hat "Non_total_Tm_arrow"
                                       uu____5849
                                      in
                                   FStar_Util.digest_of_string tkey_hash))
                      in
                   let tsym = Prims.op_Hat "Non_total_Tm_arrow_" tkey_hash
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
                     let uu____5879 =
                       let uu____5887 =
                         FStar_SMTEncoding_Term.mk_HasType t2
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5887,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5879  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t2  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5900 =
                       let uu____5908 =
                         let uu____5909 =
                           let uu____5920 =
                             let uu____5921 =
                               let uu____5926 =
                                 let uu____5927 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5927
                                  in
                               (f_has_t, uu____5926)  in
                             FStar_SMTEncoding_Util.mkImp uu____5921  in
                           ([[f_has_t]], [fsym], uu____5920)  in
                         let uu____5953 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5953 uu____5909  in
                       (uu____5908, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5900  in
                   let uu____5970 =
                     FStar_SMTEncoding_Term.mk_decls tsym tkey_hash
                       [tdecl; t_kinding; t_interp] []
                      in
                   (t2, uu____5970)))
       | FStar_Syntax_Syntax.Tm_refine uu____5971 ->
           let uu____5978 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses]  in
             let uu____5988 =
               normalize_refinement steps env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5988 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5997;
                 FStar_Syntax_Syntax.vars = uu____5998;_} ->
                 let uu____6005 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6005 with
                  | (b,f1) ->
                      let uu____6032 =
                        let uu____6033 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6033  in
                      (uu____6032, f1))
             | uu____6050 -> failwith "impossible"  in
           (match uu____5978 with
            | (x,f) ->
                let uu____6068 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6068 with
                 | (base_t,decls) ->
                     let uu____6079 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____6079 with
                      | (x1,xtm,env') ->
                          let uu____6096 = encode_formula f env'  in
                          (match uu____6096 with
                           | (refinement,decls') ->
                               let uu____6107 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6107 with
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
                                      let uu____6135 =
                                        let uu____6146 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6157 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6146
                                          uu____6157
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6135
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____6211 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____6211 <> x1) &&
                                                (let uu____6215 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____6215 <> fsym)))
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
                                    ((let uu____6248 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding")
                                         in
                                      if uu____6248
                                      then
                                        let uu____6252 =
                                          FStar_Syntax_Print.term_to_string f
                                           in
                                        let uu____6254 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6252 tkey_hash uu____6254
                                      else ());
                                     (let tsym =
                                        let uu____6261 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_refine_" uu____6261
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
                                        let uu____6281 =
                                          let uu____6289 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1
                                             in
                                          (tsym, uu____6289)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6281
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
                                        let uu____6309 =
                                          let uu____6317 =
                                            let uu____6318 =
                                              let uu____6329 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base)
                                                 in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6329)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6318
                                             in
                                          (uu____6317,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6309
                                         in
                                      let t_kinding =
                                        let uu____6343 =
                                          let uu____6351 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind)
                                             in
                                          (uu____6351,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6343
                                         in
                                      let t_interp =
                                        let uu____6365 =
                                          let uu____6373 =
                                            let uu____6374 =
                                              let uu____6385 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding)
                                                 in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6385)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6374
                                             in
                                          (uu____6373,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6365
                                         in
                                      let t_decls =
                                        [tdecl; t_kinding; t_interp; t_haseq]
                                         in
                                      let uu____6417 =
                                        let uu____6418 =
                                          let uu____6421 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls
                                              (FStar_List.append decls decls')
                                             in
                                          FStar_List.append decls' uu____6421
                                           in
                                        FStar_List.append decls uu____6418
                                         in
                                      (t2, uu____6417))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6425) ->
           let ttm =
             let uu____6443 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6443  in
           let uu____6445 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____6445 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6457 =
                    let uu____6465 =
                      let uu____6467 =
                        let uu____6469 =
                          let uu____6471 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____6471  in
                        FStar_Util.format1 "uvar_typing_%s" uu____6469  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6467
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6465)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6457  in
                let uu____6477 =
                  let uu____6478 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____6478  in
                (ttm, uu____6477))
       | FStar_Syntax_Syntax.Tm_app uu____6485 ->
           let uu____6502 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6502 with
            | (head,args_e) ->
                let uu____6549 =
                  let uu____6556 = head_redex env head  in
                  if uu____6556
                  then
                    let uu____6565 = maybe_whnf env t0  in
                    match uu____6565 with
                    | FStar_Pervasives_Native.None  -> (head, args_e)
                    | FStar_Pervasives_Native.Some t2 ->
                        FStar_Syntax_Util.head_and_args t2
                  else (head, args_e)  in
                (match uu____6549 with
                 | (head1,args_e1) ->
                     let uu____6591 =
                       let uu____6606 =
                         let uu____6607 = FStar_Syntax_Subst.compress head1
                            in
                         uu____6607.FStar_Syntax_Syntax.n  in
                       (uu____6606, args_e1)  in
                     (match uu____6591 with
                      | uu____6624 when is_arithmetic_primitive head1 args_e1
                          -> encode_arith_term env head1 args_e1
                      | uu____6639 when is_BitVector_primitive head1 args_e1
                          -> encode_BitVector_term env head1 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6657) when
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
                            FStar_Syntax_Syntax.pos = uu____6679;
                            FStar_Syntax_Syntax.vars = uu____6680;_},uu____6681),uu____6682)
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
                            FStar_Syntax_Syntax.pos = uu____6708;
                            FStar_Syntax_Syntax.vars = uu____6709;_},uu____6710),
                         (v0,uu____6712)::(v1,uu____6714)::(v2,uu____6716)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6787 = encode_term v0 env  in
                          (match uu____6787 with
                           | (v01,decls0) ->
                               let uu____6798 = encode_term v1 env  in
                               (match uu____6798 with
                                | (v11,decls1) ->
                                    let uu____6809 = encode_term v2 env  in
                                    (match uu____6809 with
                                     | (v21,decls2) ->
                                         let uu____6820 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6820,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_fvar
                         fv,(v0,uu____6823)::(v1,uu____6825)::(v2,uu____6827)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6894 = encode_term v0 env  in
                          (match uu____6894 with
                           | (v01,decls0) ->
                               let uu____6905 = encode_term v1 env  in
                               (match uu____6905 with
                                | (v11,decls1) ->
                                    let uu____6916 = encode_term v2 env  in
                                    (match uu____6916 with
                                     | (v21,decls2) ->
                                         let uu____6927 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21
                                            in
                                         (uu____6927,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of ),(arg,uu____6929)::[])
                          ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of
                         ),(arg,uu____6965)::(rng,uu____6967)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify ),uu____7018) ->
                          let e0 =
                            FStar_Syntax_Unionfind.with_uf_enabled
                              (fun uu____7042  ->
                                 let uu____7043 = FStar_List.hd args_e1  in
                                 FStar_TypeChecker_Util.reify_body_with_arg
                                   env.FStar_SMTEncoding_Env.tcenv [] head1
                                   uu____7043)
                             in
                          ((let uu____7045 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify")
                               in
                            if uu____7045
                            then
                              let uu____7050 =
                                FStar_Syntax_Print.term_to_string e0  in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu____7050
                            else ());
                           (let e =
                              let uu____7058 =
                                let uu____7063 =
                                  FStar_TypeChecker_Util.remove_reify e0  in
                                let uu____7064 = FStar_List.tl args_e1  in
                                FStar_Syntax_Syntax.mk_Tm_app uu____7063
                                  uu____7064
                                 in
                              uu____7058 FStar_Pervasives_Native.None
                                t0.FStar_Syntax_Syntax.pos
                               in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect
                         uu____7065),(arg,uu____7067)::[]) ->
                          encode_term arg env
                      | uu____7102 ->
                          let uu____7117 = encode_args args_e1 env  in
                          (match uu____7117 with
                           | (args,decls) ->
                               let encode_partial_app ht_opt =
                                 let uu____7186 = encode_term head1 env  in
                                 match uu____7186 with
                                 | (smt_head,decls') ->
                                     let app_tm = mk_Apply_args smt_head args
                                        in
                                     (match ht_opt with
                                      | uu____7206 when
                                          Prims.int_one = Prims.int_one ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type,formals,c) ->
                                          ((let uu____7278 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp")
                                               in
                                            if uu____7278
                                            then
                                              let uu____7282 =
                                                FStar_Syntax_Print.term_to_string
                                                  head1
                                                 in
                                              let uu____7284 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type
                                                 in
                                              let uu____7286 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals
                                                 in
                                              let uu____7289 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c
                                                 in
                                              let uu____7291 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1
                                                 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu____7282 uu____7284
                                                uu____7286 uu____7289
                                                uu____7291
                                            else ());
                                           (let uu____7296 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals
                                               in
                                            match uu____7296 with
                                            | (formals1,rest) ->
                                                let subst =
                                                  FStar_List.map2
                                                    (fun uu____7386  ->
                                                       fun uu____7387  ->
                                                         match (uu____7386,
                                                                 uu____7387)
                                                         with
                                                         | ((bv,uu____7417),
                                                            (a,uu____7419))
                                                             ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1
                                                   in
                                                let ty =
                                                  let uu____7451 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____7451
                                                    (FStar_Syntax_Subst.subst
                                                       subst)
                                                   in
                                                ((let uu____7455 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp")
                                                     in
                                                  if uu____7455
                                                  then
                                                    let uu____7459 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty
                                                       in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu____7459
                                                  else ());
                                                 (let uu____7464 =
                                                    let uu____7477 =
                                                      FStar_List.fold_left2
                                                        (fun uu____7512  ->
                                                           fun uu____7513  ->
                                                             fun e  ->
                                                               match 
                                                                 (uu____7512,
                                                                   uu____7513)
                                                               with
                                                               | ((t_hyps,decls1),
                                                                  (bv,uu____7554))
                                                                   ->
                                                                   let t2 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                   let uu____7582
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t2 env e
                                                                     in
                                                                   (match uu____7582
                                                                    with
                                                                    | 
                                                                    (t_hyp,decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu____7598
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp")
                                                                     in
                                                                    if
                                                                    uu____7598
                                                                    then
                                                                    let uu____7602
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____7604
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp  in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7602
                                                                    uu____7604
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
                                                    match uu____7477 with
                                                    | (t_hyps,decls1) ->
                                                        let uu____7639 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu____7648 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu____7657 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                [])
                                                           in
                                                        (match uu____7639
                                                         with
                                                         | (t_head_hyp,decls'1)
                                                             ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____7673 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm
                                                                in
                                                             (match uu____7673
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
                                                                  let uu____7695
                                                                    =
                                                                    let uu____7702
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars
                                                                     in
                                                                    if
                                                                    uu____7702
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu____7715
                                                                    =
                                                                    let uu____7717
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion
                                                                     in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7717
                                                                     in
                                                                    if
                                                                    uu____7715
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu____7730
                                                                    =
                                                                    let uu____7736
                                                                    =
                                                                    let uu____7738
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0  in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7738
                                                                     in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7736)
                                                                     in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7730);
                                                                    ([],
                                                                    cvars)))
                                                                     in
                                                                  (match uu____7695
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
                                                  match uu____7464 with
                                                  | (vars,pattern1,has_type,decls'')
                                                      ->
                                                      ((let uu____7785 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp")
                                                           in
                                                        if uu____7785
                                                        then
                                                          let uu____7789 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type
                                                             in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu____7789
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm
                                                           in
                                                        let e_typing =
                                                          let uu____7797 =
                                                            let uu____7805 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern1],
                                                                  vars,
                                                                  has_type)
                                                               in
                                                            let uu____7814 =
                                                              let uu____7816
                                                                =
                                                                let uu____7818
                                                                  =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm
                                                                   in
                                                                FStar_Util.digest_of_string
                                                                  uu____7818
                                                                 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu____7816
                                                               in
                                                            (uu____7805,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu____7814)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7797
                                                           in
                                                        let uu____7824 =
                                                          let uu____7827 =
                                                            let uu____7830 =
                                                              let uu____7833
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
                                                                uu____7833
                                                               in
                                                            FStar_List.append
                                                              decls'
                                                              uu____7830
                                                             in
                                                          FStar_List.append
                                                            decls uu____7827
                                                           in
                                                        (app_tm, uu____7824)))))))
                                      | FStar_Pervasives_Native.None  ->
                                          failwith "impossible")
                                  in
                               let encode_full_app fv =
                                 let uu____7878 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv
                                    in
                                 match uu____7878 with
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
                                        FStar_Syntax_Syntax.pos = uu____7921;
                                        FStar_Syntax_Syntax.vars = uu____7922;_},uu____7923)
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
                                        FStar_Syntax_Syntax.pos = uu____7930;
                                        FStar_Syntax_Syntax.vars = uu____7931;_},uu____7932)
                                     ->
                                     let uu____7937 =
                                       let uu____7938 =
                                         FStar_TypeChecker_Env.lookup_lid_noinst
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       FStar_All.pipe_right uu____7938
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Pervasives_Native.Some uu____7937
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu____7948 =
                                       let uu____7949 =
                                         FStar_TypeChecker_Env.lookup_lid_noinst
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       FStar_All.pipe_right uu____7949
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Pervasives_Native.Some uu____7948
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7958,(FStar_Util.Inl
                                                  t2,uu____7960),uu____7961)
                                     -> FStar_Pervasives_Native.Some t2
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____8008,(FStar_Util.Inr
                                                  c,uu____8010),uu____8011)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu____8058 -> FStar_Pervasives_Native.None
                                  in
                               (match head_type with
                                | FStar_Pervasives_Native.None  ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu____8082 =
                                      let head_type2 =
                                        let uu____8104 =
                                          normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1
                                           in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine
                                          uu____8104
                                         in
                                      let uu____8107 =
                                        curried_arrow_formals_comp head_type2
                                         in
                                      match uu____8107 with
                                      | (formals,c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu____8160 =
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
                                                uu____8160
                                               in
                                            let uu____8163 =
                                              curried_arrow_formals_comp
                                                head_type3
                                               in
                                            (match uu____8163 with
                                             | (formals1,c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c)
                                       in
                                    (match uu____8082 with
                                     | (head_type2,formals,c) ->
                                         ((let uu____8246 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp")
                                              in
                                           if uu____8246
                                           then
                                             let uu____8250 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2
                                                in
                                             let uu____8252 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals
                                                in
                                             let uu____8255 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1
                                                in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu____8250 uu____8252
                                               uu____8255
                                           else ());
                                          (match head2.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8265;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8266;_},uu____8267)
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
                                           | uu____8285 ->
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
           let uu____8374 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8374 with
            | (bs1,body1,opening) ->
                let fallback uu____8397 =
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
                  let uu____8407 =
                    let uu____8408 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8408
                     in
                  let uu____8410 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____8407, uu____8410)  in
                let is_impure rc =
                  let uu____8420 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8420 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8435 =
                          let uu____8448 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8448
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____8435 with
                         | (t2,uu____8451,uu____8452) -> t2)
                    | FStar_Pervasives_Native.Some t2 -> t2  in
                  let uu____8470 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____8470
                  then
                    let uu____8475 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8475
                  else
                    (let uu____8478 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____8478
                     then
                       let uu____8483 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8483
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8491 =
                         let uu____8497 =
                           let uu____8499 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8499
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8497)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8491);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8504 =
                       (is_impure rc) &&
                         (let uu____8507 =
                            FStar_SMTEncoding_Util.is_smt_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____8507)
                        in
                     if uu____8504
                     then fallback ()
                     else
                       (let uu____8516 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8516 with
                        | (vars,guards,envbody,decls,uu____8541) ->
                            let body2 =
                              let uu____8555 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____8555
                              then
                                FStar_Syntax_Unionfind.with_uf_enabled
                                  (fun uu____8559  ->
                                     FStar_TypeChecker_Util.reify_body
                                       env.FStar_SMTEncoding_Env.tcenv []
                                       body1)
                              else body1  in
                            let uu____8562 = encode_term body2 envbody  in
                            (match uu____8562 with
                             | (body3,decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect
                                    in
                                 let uu____8575 =
                                   let uu____8584 = codomain_eff rc  in
                                   match uu____8584 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8603 = encode_term tfun env
                                          in
                                       (match uu____8603 with
                                        | (t2,decls1) ->
                                            ((FStar_Pervasives_Native.Some t2),
                                              decls1))
                                    in
                                 (match uu____8575 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8637 =
                                          let uu____8648 =
                                            let uu____8649 =
                                              let uu____8654 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8654, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8649
                                             in
                                          ([], vars, uu____8648)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8637
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____8662 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t2 ->
                                            let uu____8678 =
                                              let uu____8681 =
                                                let uu____8692 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t2
                                                   in
                                                FStar_List.append uu____8692
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8681
                                               in
                                            let uu____8719 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t2)
                                               in
                                            (uu____8678, uu____8719)
                                         in
                                      (match uu____8662 with
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
                                           ((let uu____8742 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp")
                                                in
                                             if uu____8742
                                             then
                                               let uu____8747 =
                                                 let uu____8749 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8749
                                                   (FStar_String.concat ", ")
                                                  in
                                               let uu____8759 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3
                                                  in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8747 uu____8759
                                             else ());
                                            (let uu____8764 =
                                               is_an_eta_expansion env vars
                                                 body3
                                                in
                                             match uu____8764 with
                                             | FStar_Pervasives_Native.Some
                                                 t2 ->
                                                 ((let uu____8773 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp")
                                                      in
                                                   if uu____8773
                                                   then
                                                     let uu____8778 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t2
                                                        in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8778
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
                                                   let uu____8791 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8791
                                                    in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None)
                                                    in
                                                 let f =
                                                   let uu____8800 =
                                                     let uu____8808 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1
                                                        in
                                                     (fsym, uu____8808)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8800
                                                    in
                                                 let app = mk_Apply f vars
                                                    in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8822 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8830
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue))
                                                              in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8822
                                                             is_pure
                                                            in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8831 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax)
                                                          in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym
                                                          in
                                                       let uu____8845 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                          in
                                                       [uu____8845]
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
                                                       let uu____8853 =
                                                         let uu____8854 =
                                                           let uu____8862 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t)
                                                              in
                                                           (uu____8862,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name)
                                                            in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8854
                                                          in
                                                       [uu____8853]
                                                    in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym
                                                      in
                                                   let uu____8877 =
                                                     let uu____8885 =
                                                       let uu____8886 =
                                                         let uu____8897 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3)
                                                            in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8897)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8886
                                                        in
                                                     (uu____8885,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name)
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8877
                                                    in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]
                                                    in
                                                 let uu____8911 =
                                                   let uu____8912 =
                                                     let uu____8915 =
                                                       let uu____8918 =
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
                                                         decls'' uu____8918
                                                        in
                                                     FStar_List.append decls'
                                                       uu____8915
                                                      in
                                                   FStar_List.append decls
                                                     uu____8912
                                                    in
                                                 (f, uu____8911)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8921,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8922;
                          FStar_Syntax_Syntax.lbunivs = uu____8923;
                          FStar_Syntax_Syntax.lbtyp = uu____8924;
                          FStar_Syntax_Syntax.lbeff = uu____8925;
                          FStar_Syntax_Syntax.lbdef = uu____8926;
                          FStar_Syntax_Syntax.lbattrs = uu____8927;
                          FStar_Syntax_Syntax.lbpos = uu____8928;_}::uu____8929),uu____8930)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8964;
                FStar_Syntax_Syntax.lbtyp = t11;
                FStar_Syntax_Syntax.lbeff = uu____8966;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8968;
                FStar_Syntax_Syntax.lbpos = uu____8969;_}::[]),e2)
           -> encode_let x t11 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false ,uu____8996::uu____8997),uu____8998) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____9021,lbs),uu____9023) ->
           let names =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb  ->
                     let uu____9076 = lb  in
                     match uu____9076 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____9083;
                         FStar_Syntax_Syntax.lbtyp = uu____9084;
                         FStar_Syntax_Syntax.lbeff = uu____9085;
                         FStar_Syntax_Syntax.lbdef = uu____9086;
                         FStar_Syntax_Syntax.lbattrs = uu____9087;
                         FStar_Syntax_Syntax.lbpos = uu____9088;_} ->
                         let x = FStar_Util.left lbname  in
                         let uu____9104 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname
                            in
                         let uu____9106 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         (uu____9104, uu____9106)))
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
              let uu____9164 =
                let uu____9169 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____9169 env  in
              match uu____9164 with
              | (ee1,decls1) ->
                  let uu____9194 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9194 with
                   | (xs,e21) ->
                       let uu____9219 = FStar_List.hd xs  in
                       (match uu____9219 with
                        | (x1,uu____9237) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____9243 = encode_body e21 env'  in
                            (match uu____9243 with
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
            let uu____9273 =
              let uu____9281 =
                let uu____9282 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9282  in
              FStar_SMTEncoding_Env.gen_term_var env uu____9281  in
            match uu____9273 with
            | (scrsym,scr',env1) ->
                let uu____9292 = encode_term e env1  in
                (match uu____9292 with
                 | (scr,decls) ->
                     let uu____9303 =
                       let encode_branch b uu____9332 =
                         match uu____9332 with
                         | (else_case,decls1) ->
                             let uu____9351 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9351 with
                              | (p,w,br) ->
                                  let uu____9377 = encode_pat env1 p  in
                                  (match uu____9377 with
                                   | (env0,pattern1) ->
                                       let guard = pattern1.guard scr'  in
                                       let projections =
                                         pattern1.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9414  ->
                                                   match uu____9414 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____9421 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9443 =
                                               encode_term w1 env2  in
                                             (match uu____9443 with
                                              | (w2,decls2) ->
                                                  let uu____9456 =
                                                    let uu____9457 =
                                                      let uu____9462 =
                                                        let uu____9463 =
                                                          let uu____9468 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9468)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9463
                                                         in
                                                      (guard, uu____9462)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9457
                                                     in
                                                  (uu____9456, decls2))
                                          in
                                       (match uu____9421 with
                                        | (guard1,decls2) ->
                                            let uu____9483 =
                                              encode_br br env2  in
                                            (match uu____9483 with
                                             | (br1,decls3) ->
                                                 let uu____9496 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9496,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9303 with
                      | (match_tm,decls1) ->
                          let uu____9517 =
                            let uu____9518 =
                              let uu____9529 =
                                let uu____9536 =
                                  let uu____9541 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____9541, scr)  in
                                [uu____9536]  in
                              (uu____9529, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____9518
                              FStar_Range.dummyRange
                             in
                          (uu____9517, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____9564 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____9564
       then
         let uu____9567 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9567
       else ());
      (let uu____9572 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9572 with
       | (vars,pat_term) ->
           let uu____9589 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9631  ->
                     fun v  ->
                       match uu____9631 with
                       | (env1,vars1) ->
                           let uu____9667 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v  in
                           (match uu____9667 with
                            | (xx,uu____9686,env2) ->
                                let uu____9690 =
                                  let uu____9697 =
                                    let uu____9702 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v, uu____9702)  in
                                  uu____9697 :: vars1  in
                                (env2, uu____9690))) (env, []))
              in
           (match uu____9589 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9757 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9758 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9759 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9767 = encode_const c env1  in
                      (match uu____9767 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9775::uu____9776 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9780 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9803 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____9803 with
                        | (uu____9811,uu____9812::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9817 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9853  ->
                                  match uu____9853 with
                                  | (arg,uu____9863) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9872 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9872))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9904) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9935 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9960 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____10006  ->
                                  match uu____10006 with
                                  | (arg,uu____10022) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____10031 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____10031))
                         in
                      FStar_All.pipe_right uu____9960 FStar_List.flatten
                   in
                let pat_term1 uu____10062 = encode_term pat_term env1  in
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
      let uu____10072 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10120  ->
                fun uu____10121  ->
                  match (uu____10120, uu____10121) with
                  | ((tms,decls),(t,uu____10161)) ->
                      let uu____10188 = encode_term t env  in
                      (match uu____10188 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____10072 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10266  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1428_10275 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1428_10275.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1428_10275.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1428_10275.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1428_10275.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1428_10275.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1428_10275.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1428_10275.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1428_10275.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1428_10275.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1428_10275.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1433_10292 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1433_10292.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1433_10292.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1433_10292.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1433_10292.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1433_10292.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1433_10292.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1433_10292.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1433_10292.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1433_10292.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1433_10292.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____10308 = FStar_Syntax_Util.head_and_args t  in
        match uu____10308 with
        | (head,args) ->
            let head1 = FStar_Syntax_Util.un_uinst head  in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10371::(x,uu____10373)::(t1,uu____10375)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10442 = encode_term x env1  in
                 (match uu____10442 with
                  | (x1,decls) ->
                      let uu____10453 = encode_term t1 env1  in
                      (match uu____10453 with
                       | (t2,decls') ->
                           let uu____10464 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10464, (FStar_List.append decls decls'))))
             | uu____10465 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10508  ->
             match uu____10508 with
             | (pats_l1,decls) ->
                 let uu____10553 =
                   FStar_List.fold_right
                     (fun uu____10588  ->
                        fun uu____10589  ->
                          match (uu____10588, uu____10589) with
                          | ((p,uu____10631),(pats1,decls1)) ->
                              let uu____10666 = encode_smt_pattern p  in
                              (match uu____10666 with
                               | (t,d) ->
                                   let uu____10681 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10681 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10698 =
                                            let uu____10704 =
                                              let uu____10706 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10708 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10706 uu____10708
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10704)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10698);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10553 with
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
        let uu____10768 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10768
        then
          let uu____10773 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10775 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10773 uu____10775
        else ()  in
      let enc f r l =
        let uu____10817 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10849 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10849 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10817 with
        | (decls,args) ->
            let uu____10880 =
              let uu___1497_10881 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1497_10881.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1497_10881.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10880, decls)
         in
      let const_op f r uu____10916 =
        let uu____10929 = f r  in (uu____10929, [])  in
      let un_op f l =
        let uu____10952 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10952  in
      let bin_op f uu___2_10972 =
        match uu___2_10972 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10983 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11024 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11049  ->
                 match uu____11049 with
                 | (t,uu____11065) ->
                     let uu____11070 = encode_formula t env  in
                     (match uu____11070 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11024 with
        | (decls,phis) ->
            let uu____11099 =
              let uu___1527_11100 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1527_11100.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1527_11100.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11099, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11163  ->
               match uu____11163 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11184) -> false
                    | uu____11187 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu____11206 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11206
        else
          (let uu____11223 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11223 r rf)
         in
      let eq3_op r args =
        let n = FStar_List.length args  in
        if n = (Prims.of_int (4))
        then
          let uu____11291 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11323 =
                       let uu____11328 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11329 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11328, uu____11329)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11323
                 | uu____11330 -> failwith "Impossible")
             in
          uu____11291 r args
        else
          (let uu____11336 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n)
              in
           failwith uu____11336)
         in
      let h_equals_op r args =
        let n = FStar_List.length args  in
        if n = (Prims.of_int (4))
        then
          let uu____11398 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11430 =
                       let uu____11435 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11436 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11435, uu____11436)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11430
                 | uu____11437 -> failwith "Impossible")
             in
          uu____11398 r args
        else
          (let uu____11443 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n)
              in
           failwith uu____11443)
         in
      let mk_imp r uu___3_11472 =
        match uu___3_11472 with
        | (lhs,uu____11478)::(rhs,uu____11480)::[] ->
            let uu____11521 = encode_formula rhs env  in
            (match uu____11521 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11536) ->
                      (l1, decls1)
                  | uu____11541 ->
                      let uu____11542 = encode_formula lhs env  in
                      (match uu____11542 with
                       | (l2,decls2) ->
                           let uu____11553 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11553, (FStar_List.append decls1 decls2)))))
        | uu____11554 -> failwith "impossible"  in
      let mk_ite r uu___4_11582 =
        match uu___4_11582 with
        | (guard,uu____11588)::(_then,uu____11590)::(_else,uu____11592)::[]
            ->
            let uu____11649 = encode_formula guard env  in
            (match uu____11649 with
             | (g,decls1) ->
                 let uu____11660 = encode_formula _then env  in
                 (match uu____11660 with
                  | (t,decls2) ->
                      let uu____11671 = encode_formula _else env  in
                      (match uu____11671 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11683 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11713 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11713  in
      let connectives =
        let uu____11743 =
          let uu____11768 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11768)  in
        let uu____11811 =
          let uu____11838 =
            let uu____11863 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11863)  in
          let uu____11906 =
            let uu____11933 =
              let uu____11960 =
                let uu____11985 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11985)  in
              let uu____12028 =
                let uu____12055 =
                  let uu____12082 =
                    let uu____12107 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____12107)  in
                  [uu____12082;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12055  in
              uu____11960 :: uu____12028  in
            (FStar_Parser_Const.imp_lid, mk_imp) :: uu____11933  in
          uu____11838 :: uu____11906  in
        uu____11743 :: uu____11811  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12652 = encode_formula phi' env  in
            (match uu____12652 with
             | (phi2,decls) ->
                 let uu____12663 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12663, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12665 ->
            let uu____12672 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12672 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12711 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12711 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12723;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12725;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12727;
                 FStar_Syntax_Syntax.lbpos = uu____12728;_}::[]),e2)
            ->
            let uu____12755 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12755 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head1 = FStar_Syntax_Util.un_uinst head  in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12808::(x,uu____12810)::(t,uu____12812)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12879 = encode_term x env  in
                 (match uu____12879 with
                  | (x1,decls) ->
                      let uu____12890 = encode_term t env  in
                      (match uu____12890 with
                       | (t1,decls') ->
                           let uu____12901 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12901, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12904)::(msg,uu____12906)::(phi2,uu____12908)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12975 =
                   let uu____12985 =
                     let uu____12988 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_range r
                        in
                     uu____12988 false FStar_Syntax_Embeddings.id_norm_cb  in
                   let uu____12996 =
                     let uu____13000 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_string msg
                        in
                     uu____13000 false FStar_Syntax_Embeddings.id_norm_cb  in
                   (uu____12985, uu____12996)  in
                 (match uu____12975 with
                  | (FStar_Pervasives_Native.Some
                     r1,FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | (FStar_Pervasives_Native.None
                     ,FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, (phi2.FStar_Syntax_Syntax.pos), false))))
                          FStar_Pervasives_Native.None
                          phi2.FStar_Syntax_Syntax.pos
                         in
                      fallback phi3
                  | uu____13052 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____13064)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____13099 ->
                 let encode_valid uu____13123 =
                   let uu____13124 = encode_term phi1 env  in
                   match uu____13124 with
                   | (tt,decls) ->
                       let tt1 =
                         let uu____13136 =
                           let uu____13138 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng
                              in
                           let uu____13139 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos
                              in
                           FStar_Range.rng_included uu____13138 uu____13139
                            in
                         if uu____13136
                         then tt
                         else
                           (let uu___1716_13143 = tt  in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___1716_13143.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___1716_13143.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            })
                          in
                       let uu____13144 = FStar_SMTEncoding_Term.mk_Valid tt1
                          in
                       (uu____13144, decls)
                    in
                 let uu____13145 = head_redex env head1  in
                 if uu____13145
                 then
                   let uu____13152 = maybe_whnf env head1  in
                   (match uu____13152 with
                    | FStar_Pervasives_Native.None  -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu____13162 ->
            let uu____13163 = encode_term phi1 env  in
            (match uu____13163 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____13175 =
                     let uu____13177 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____13178 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____13177 uu____13178  in
                   if uu____13175
                   then tt
                   else
                     (let uu___1728_13182 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1728_13182.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1728_13182.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____13183 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____13183, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13227 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13227 with
        | (vars,guards,env2,decls,uu____13266) ->
            let uu____13279 = encode_smt_patterns ps env2  in
            (match uu____13279 with
             | (pats,decls') ->
                 let uu____13316 = encode_formula body env2  in
                 (match uu____13316 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13348;
                             FStar_SMTEncoding_Term.rng = uu____13349;_}::[])::[]
                            when
                            let uu____13369 =
                              FStar_Ident.string_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13369 = gf -> []
                        | uu____13372 -> guards  in
                      let uu____13377 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13377, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13388 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13388 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13397 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13503  ->
                     match uu____13503 with
                     | (l,uu____13528) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13397 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13597,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13689 = encode_q_body env vars pats body  in
             match uu____13689 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13734 =
                     let uu____13745 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13745)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13734
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13776 = encode_q_body env vars pats body  in
             match uu____13776 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13820 =
                   let uu____13821 =
                     let uu____13832 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13832)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13821
                    in
                 (uu____13820, decls))))
