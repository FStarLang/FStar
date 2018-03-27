open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit) =
  fun env  ->
    fun errs  ->
      let uu____17 = FStar_TypeChecker_Env.get_range env  in
      let uu____18 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____17 uu____18
  
let (is_type : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26 =
      let uu____27 = FStar_Syntax_Subst.compress t  in
      uu____27.FStar_Syntax_Syntax.n  in
    match uu____26 with
    | FStar_Syntax_Syntax.Tm_type uu____30 -> true
    | uu____31 -> false
  
let (t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    let uu____41 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____41
      (FStar_List.filter
         (fun uu____55  ->
            match uu____55 with
            | (x,uu____61) -> is_type x.FStar_Syntax_Syntax.sort))
  
let (new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____73 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____75 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____75)
           in
        if uu____73
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____77 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Rel.new_uvar uu____77 bs k
  
let (new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____84 = new_uvar_aux env k  in
      FStar_Pervasives_Native.fst uu____84
  
let (as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar) =
  fun uu___77_93  ->
    match uu___77_93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____95);
        FStar_Syntax_Syntax.pos = uu____96;
        FStar_Syntax_Syntax.vars = uu____97;_} -> uv
    | uu____124 -> failwith "Impossible"
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____149 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____149 with
          | FStar_Pervasives_Native.Some (uu____172::(tm,uu____174)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____226 ->
              let uu____237 = new_uvar_aux env k  in
              (match uu____237 with
               | (t,u) ->
                   let g =
                     let uu___96_257 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u  in
                         (reason, env, uu____286, t, k, r)  in
                       [uu____273]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___96_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___96_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___96_257.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____258
                     }  in
                   let uu____311 =
                     let uu____318 =
                       let uu____323 = as_uvar u  in (uu____323, r)  in
                     [uu____318]  in
                   (t, uu____311, g))
  
let (check_uvars :
  FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____351 =
        let uu____352 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____352  in
      if uu____351
      then
        let us =
          let uu____358 =
            let uu____361 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____379  ->
                 match uu____379 with
                 | (x,uu____385) -> FStar_Syntax_Print.uvar_to_string x)
              uu____361
             in
          FStar_All.pipe_right uu____358 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____392 =
            let uu____397 =
              let uu____398 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____398
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____397)  in
          FStar_Errors.log_issue r uu____392);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____411  ->
      match uu____411 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____421;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____423;
          FStar_Syntax_Syntax.lbpos = uu____424;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder1 scope a =
                   let uu____473 =
                     let uu____474 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____474.FStar_Syntax_Syntax.n  in
                   match uu____473 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____481 = FStar_Syntax_Util.type_u ()  in
                       (match uu____481 with
                        | (k,uu____491) ->
                            let t2 =
                              let uu____493 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____493
                                FStar_Pervasives_Native.fst
                               in
                            ((let uu___97_503 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___97_503.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___97_503.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____504 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____541) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____548) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____611) ->
                       let uu____632 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____692  ->
                                 fun uu____693  ->
                                   match (uu____692, uu____693) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____771 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____771 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____632 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____883 = aux must_check_ty1 scope body  in
                            (match uu____883 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____912 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____912
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____919 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____919
                                   then
                                     let uu____920 =
                                       FStar_Range.string_of_range r  in
                                     let uu____921 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____922 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____920 uu____921 uu____922
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____932 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____946 =
                            let uu____951 =
                              let uu____952 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____952
                                FStar_Pervasives_Native.fst
                               in
                            FStar_Util.Inl uu____951  in
                          (uu____946, false))
                    in
                 let uu____965 =
                   let uu____974 = t_binders env  in aux false uu____974 e
                    in
                 match uu____965 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____999 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____999
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1003 =
                                let uu____1008 =
                                  let uu____1009 =
                                    FStar_Syntax_Print.comp_to_string c  in
                                  FStar_Util.format1
                                    "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                    uu____1009
                                   in
                                (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                  uu____1008)
                                 in
                              FStar_Errors.raise_error uu____1003 rng)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____1017 ->
               let uu____1018 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1018 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____1098 =
              let uu____1103 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1103 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1108;
                  FStar_Syntax_Syntax.vars = uu____1109;_} ->
                  let uu____1112 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1112 with
                   | (t,uu____1122) ->
                       let uu____1123 = new_uvar env1 t  in
                       (uu____1123, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1098 with
            | (t_x,guard) ->
                ((let uu___98_1132 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___98_1132.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___98_1132.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard)
             in
          let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr,FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu____1201 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1209) ->
                let uu____1214 = FStar_Syntax_Util.type_u ()  in
                (match uu____1214 with
                 | (k,uu____1240) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___99_1243 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___99_1243.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___99_1243.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1244 =
                       let uu____1249 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1249 t
                        in
                     (match uu____1244 with
                      | (e,u) ->
                          let p2 =
                            let uu___100_1275 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___100_1275.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1285 = check_bv env1 x  in
                (match uu____1285 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1326 = check_bv env1 x  in
                (match uu____1326 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1383 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1519  ->
                          fun uu____1520  ->
                            match (uu____1519, uu____1520) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1718 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1718 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1794 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1794, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1383 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1925 =
                         let uu____1926 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1927 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1926 uu____1927
                          in
                       uu____1925 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1934 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1945 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1956 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1934, uu____1945, uu____1956, env2, e, guard,
                       (let uu___101_1978 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___101_1978.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____2062  ->
                       match uu____2062 with
                       | (p2,imp) ->
                           let uu____2081 = elaborate_pat env1 p2  in
                           (uu____2081, imp)) pats
                   in
                let uu____2086 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2086 with
                 | (uu____2093,t) ->
                     let uu____2095 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2095 with
                      | (f,uu____2111) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2233::uu____2234) ->
                                let uu____2277 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2277
                            | (uu____2286::uu____2287,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2365  ->
                                        match uu____2365 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2392 =
                                                     let uu____2395 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2395
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2392
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2397 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2397, true)
                                             | uu____2402 ->
                                                 let uu____2405 =
                                                   let uu____2410 =
                                                     let uu____2411 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2411
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2410)
                                                    in
                                                 let uu____2412 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2405 uu____2412)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2486,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2487)) when p_imp ->
                                     let uu____2490 = aux formals' pats'  in
                                     (p2, true) :: uu____2490
                                 | (uu____2507,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2515 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2515
                                        in
                                     let uu____2516 = aux formals' pats2  in
                                     (p3, true) :: uu____2516
                                 | (uu____2533,imp) ->
                                     let uu____2539 =
                                       let uu____2546 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2546)  in
                                     let uu____2549 = aux formals' pats'  in
                                     uu____2539 :: uu____2549)
                             in
                          let uu___102_2564 = p1  in
                          let uu____2567 =
                            let uu____2568 =
                              let uu____2581 = aux f pats1  in
                              (fv, uu____2581)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2568  in
                          {
                            FStar_Syntax_Syntax.v = uu____2567;
                            FStar_Syntax_Syntax.p =
                              (uu___102_2564.FStar_Syntax_Syntax.p)
                          }))
            | uu____2598 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2634 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2634 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2692 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2692 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2718 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2718
                       p3.FStar_Syntax_Syntax.p
                 | uu____2741 -> (b, a, w, arg, guard, p3))
             in
          let uu____2750 = one_pat true env p  in
          match uu____2750 with
          | (b,uu____2780,uu____2781,tm,guard,p1) -> (b, tm, guard, p1)
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2827,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2829)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2834,uu____2835) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2839 =
                    let uu____2840 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2841 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2840 uu____2841
                     in
                  failwith uu____2839)
               else ();
               (let uu____2844 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2844
                then
                  let uu____2845 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2846 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2845
                    uu____2846
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___103_2850 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___103_2850.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___103_2850.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2854 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2854
                then
                  let uu____2855 =
                    let uu____2856 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2857 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2856 uu____2857
                     in
                  failwith uu____2855
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___104_2861 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___104_2861.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___104_2861.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2863),uu____2864) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2886 =
                  let uu____2887 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2887  in
                if uu____2886
                then
                  let uu____2888 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2888
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2907;
                FStar_Syntax_Syntax.vars = uu____2908;_},args))
              ->
              ((let uu____2947 =
                  let uu____2948 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2948 Prims.op_Negation  in
                if uu____2947
                then
                  let uu____2949 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2949
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3085)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3160) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3197) ->
                           let pat =
                             let uu____3219 = aux argpat e2  in
                             let uu____3220 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3219, uu____3220)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3225 ->
                      let uu____3248 =
                        let uu____3249 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3250 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3249 uu____3250
                         in
                      failwith uu____3248
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3262;
                     FStar_Syntax_Syntax.vars = uu____3263;_},uu____3264);
                FStar_Syntax_Syntax.pos = uu____3265;
                FStar_Syntax_Syntax.vars = uu____3266;_},args))
              ->
              ((let uu____3309 =
                  let uu____3310 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3310 Prims.op_Negation  in
                if uu____3309
                then
                  let uu____3311 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3311
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3447)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3522) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3559) ->
                           let pat =
                             let uu____3581 = aux argpat e2  in
                             let uu____3582 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3581, uu____3582)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3587 ->
                      let uu____3610 =
                        let uu____3611 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3612 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3611 uu____3612
                         in
                      failwith uu____3610
                   in
                match_args [] args argpats))
          | uu____3621 ->
              let uu____3626 =
                let uu____3627 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3628 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3629 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3627 uu____3628 uu____3629
                 in
              failwith uu____3626
           in
        aux p exp
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____3666 =
      match uu____3666 with
      | (p,i) ->
          let uu____3683 = decorated_pattern_as_term p  in
          (match uu____3683 with
           | (vars,te) ->
               let uu____3706 =
                 let uu____3711 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3711)  in
               (vars, uu____3706))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3725 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3725)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3729 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3729)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3733 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3733)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3754 =
          let uu____3769 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3769 FStar_List.unzip  in
        (match uu____3754 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3879 =
               let uu____3880 =
                 let uu____3881 =
                   let uu____3896 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3896, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3881  in
               mk1 uu____3880  in
             (vars1, uu____3879))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3926,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3936,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3950 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3974)::[] -> wp
      | uu____3991 ->
          let uu____4000 =
            let uu____4001 =
              let uu____4002 =
                FStar_List.map
                  (fun uu____4012  ->
                     match uu____4012 with
                     | (x,uu____4018) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4002 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4001
             in
          failwith uu____4000
       in
    let uu____4023 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4023, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4037 = destruct_comp c  in
        match uu____4037 with
        | (u,uu____4045,wp) ->
            let uu____4047 =
              let uu____4056 =
                let uu____4057 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4057  in
              [uu____4056]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4047;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4067 =
          let uu____4074 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4075 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4074 uu____4075  in
        match uu____4067 with | (m,uu____4077,uu____4078) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4088 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4088
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____4125 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4125 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4162 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4162 with
             | (a,kwp) ->
                 let uu____4193 = destruct_comp m1  in
                 let uu____4200 = destruct_comp m2  in
                 ((md, a, kwp), uu____4193, uu____4200))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____4262 =
              let uu____4263 =
                let uu____4272 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4272]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4263;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4262
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          let uu____4304 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4304
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____4312 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4312
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4315  ->
           let uu____4316 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4316)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4320 =
      let uu____4321 = FStar_Syntax_Subst.compress t  in
      uu____4321.FStar_Syntax_Syntax.n  in
    match uu____4320 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4324 -> true
    | uu____4337 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4375 =
                let uu____4376 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4376  in
              if uu____4375
              then f
              else (let uu____4378 = reason1 ()  in label uu____4378 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___105_4389 = g  in
            let uu____4390 =
              let uu____4391 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4391  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4390;
              FStar_TypeChecker_Env.deferred =
                (uu___105_4389.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___105_4389.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___105_4389.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4405 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4405
        then c
        else
          (let uu____4407 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4407
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4446 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4446]  in
                       let us =
                         let uu____4450 =
                           let uu____4453 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4453]  in
                         u_res :: uu____4450  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4457 =
                         let uu____4458 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4459 =
                           let uu____4460 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4461 =
                             let uu____4464 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4465 =
                               let uu____4468 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4468]  in
                             uu____4464 :: uu____4465  in
                           uu____4460 :: uu____4461  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4458 uu____4459
                          in
                       uu____4457 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4472 = destruct_comp c1  in
              match uu____4472 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____4499  ->
             let uu____4500 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4500)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___78_4507  ->
            match uu___78_4507 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4508 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____4524 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4524))
               &&
               (let uu____4531 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4531 with
                | (head1,uu____4545) ->
                    let uu____4562 =
                      let uu____4563 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4563.FStar_Syntax_Syntax.n  in
                    (match uu____4562 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4567 =
                           let uu____4568 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4568
                            in
                         Prims.op_Negation uu____4567
                     | uu____4569 -> true)))
              &&
              (let uu____4571 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4571)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____4589 =
              let uu____4590 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4590  in
            if uu____4589
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4592 = FStar_Syntax_Util.is_unit t  in
               if uu____4592
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____4598 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4598
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4600 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4600 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4608 =
                             let uu____4609 =
                               let uu____4610 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4611 =
                                 let uu____4612 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4613 =
                                   let uu____4616 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4616]  in
                                 uu____4612 :: uu____4613  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4610
                                 uu____4611
                                in
                             uu____4609 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4608)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4620 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4620
           then
             let uu____4621 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4622 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4623 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4621 uu____4622 uu____4623
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4634 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___79_4638  ->
              match uu___79_4638 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4639 -> false))
       in
    if uu____4634
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___80_4648  ->
              match uu___80_4648 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4661 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4661
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4664 = destruct_comp c1  in
           match uu____4664 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4678 =
                   let uu____4679 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4680 =
                     let uu____4681 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4682 =
                       let uu____4685 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4686 =
                         let uu____4689 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4689]  in
                       uu____4685 :: uu____4686  in
                     uu____4681 :: uu____4682  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4679 uu____4680  in
                 uu____4678 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4692 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4692)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4707 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4709 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4709
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4712 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4712 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____4745 = destruct_comp c1  in
               match uu____4745 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____4759 =
                       let uu____4760 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____4761 =
                         let uu____4762 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____4763 =
                           let uu____4766 =
                             let uu____4767 =
                               let uu____4768 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____4768 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____4767
                              in
                           let uu____4769 =
                             let uu____4772 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____4772]  in
                           uu____4766 :: uu____4769  in
                         uu____4762 :: uu____4763  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4760 uu____4761
                        in
                     uu____4759 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____4807 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____4807
            then (lc, g0)
            else
              (let flags1 =
                 let uu____4816 =
                   let uu____4823 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____4823
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4816 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____4843 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___81_4851  ->
                               match uu___81_4851 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____4854 -> []))
                        in
                     FStar_List.append flags1 uu____4843
                  in
               let strengthen uu____4858 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____4862 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____4862 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____4865 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4865
                          then
                            let uu____4866 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____4867 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____4866 uu____4867
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____4869 =
                 let uu____4870 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____4870
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____4869,
                 (let uu___106_4872 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___106_4872.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___106_4872.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___106_4872.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___82_4877  ->
            match uu___82_4877 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4878 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____4895 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4895
          then e
          else
            (let uu____4897 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4899 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4899)
                in
             if uu____4897
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____4937  ->
            match uu____4937 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4955 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4955 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4963 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4963
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4970 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____4970
                       then
                         let uu____4973 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____4973
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4977 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____4977
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4982 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____4982
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____4986 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____4986
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____4993 =
                  let uu____4994 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____4994
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____5008  ->
                          let uu____5009 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5010 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5012 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5009 uu____5010 uu____5012);
                     (let aux uu____5024 =
                        let uu____5025 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5025
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5046 ->
                              let uu____5047 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5047
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5066 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5066
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5133 =
                              let uu____5138 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5138, reason)  in
                            FStar_Util.Inl uu____5133
                        | uu____5145 -> aux ()  in
                      let try_simplify uu____5167 =
                        let rec maybe_close t x c =
                          let uu____5178 =
                            let uu____5179 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5179.FStar_Syntax_Syntax.n  in
                          match uu____5178 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5183) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5189 -> c  in
                        let uu____5190 =
                          let uu____5191 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5191  in
                        if uu____5190
                        then
                          let uu____5202 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____5202
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5216 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5216))
                        else
                          (let uu____5226 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5226
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5236 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5236
                              then
                                let uu____5245 =
                                  let uu____5250 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5250, "both gtot")  in
                                FStar_Util.Inl uu____5245
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5274 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5276 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____5276)
                                        in
                                     if uu____5274
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___107_5287 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___107_5287.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___107_5287.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____5288 =
                                         let uu____5293 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____5293, "c1 Tot")  in
                                       FStar_Util.Inl uu____5288
                                     else aux ()
                                 | uu____5299 -> aux ())))
                         in
                      let uu____5308 = try_simplify ()  in
                      match uu____5308 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5328  ->
                                let uu____5329 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5329);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5338  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5353 = lift_and_destruct env c11 c21
                                 in
                              match uu____5353 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5410 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5410]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5412 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5412]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____5425 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5426 =
                                      let uu____5429 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5430 =
                                        let uu____5433 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5434 =
                                          let uu____5437 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5438 =
                                            let uu____5441 =
                                              let uu____5442 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5442
                                               in
                                            [uu____5441]  in
                                          uu____5437 :: uu____5438  in
                                        uu____5433 :: uu____5434  in
                                      uu____5429 :: uu____5430  in
                                    uu____5425 :: uu____5426  in
                                  let wp =
                                    let uu____5446 =
                                      let uu____5447 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5447 wp_args
                                       in
                                    uu____5446 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____5466 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5466 with
                              | (m,uu____5474,lift2) ->
                                  let c23 =
                                    let uu____5477 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5477
                                     in
                                  let uu____5478 = destruct_comp c12  in
                                  (match uu____5478 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5492 =
                                           let uu____5493 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____5494 =
                                             let uu____5495 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____5496 =
                                               let uu____5499 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____5499]  in
                                             uu____5495 :: uu____5496  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5493 uu____5494
                                            in
                                         uu____5492
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____5505 = destruct_comp c1_typ  in
                            match uu____5505 with
                            | (u_res_t1,res_t1,uu____5514) ->
                                let uu____5515 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____5515
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____5518 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____5518
                                   then
                                     (debug1
                                        (fun uu____5526  ->
                                           let uu____5527 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____5528 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5527 uu____5528);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5531 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5533 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____5533)
                                         in
                                      if uu____5531
                                      then
                                        let e1' =
                                          let uu____5555 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____5555
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____5566  ->
                                              let uu____5567 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____5568 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5567 uu____5568);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5580  ->
                                              let uu____5581 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5582 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5581 uu____5582);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____5585 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5585
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____5597 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____5613 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____5613)
           in
        let flags1 =
          if should_return1
          then
            let uu____5619 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____5619
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____5627 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____5631 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____5631
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____5633 =
              let uu____5634 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____5634  in
            (if uu____5633
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___108_5637 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___108_5637.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___108_5637.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___108_5637.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____5648 =
                 let uu____5651 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____5651
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5648
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____5656 =
               let uu____5657 =
                 let uu____5658 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5658
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____5657  in
             FStar_Syntax_Util.comp_set_flags uu____5656 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____5681  ->
              match uu____5681 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____5693 =
                      ((let uu____5696 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5696) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5693
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5706 =
        let uu____5707 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5707  in
      FStar_Syntax_Syntax.fvar uu____5706 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5766  ->
                 match uu____5766 with
                 | (uu____5779,eff_label,uu____5781,uu____5782) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____5791 =
          let uu____5798 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5830  ->
                    match uu____5830 with
                    | (uu____5843,uu____5844,flags1,uu____5846) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___83_5858  ->
                                match uu___83_5858 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5859 -> false))))
             in
          if uu____5798
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____5791 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5880 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____5882 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5882
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5902 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____5903 =
                     let uu____5904 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____5905 =
                       let uu____5906 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____5907 =
                         let uu____5910 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____5911 =
                           let uu____5914 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____5915 =
                             let uu____5918 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____5918]  in
                           uu____5914 :: uu____5915  in
                         uu____5910 :: uu____5911  in
                       uu____5906 :: uu____5907  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5904 uu____5905  in
                   uu____5903 FStar_Pervasives_Native.None uu____5902  in
                 let default_case =
                   let post_k =
                     let uu____5925 =
                       let uu____5932 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____5932]  in
                     let uu____5933 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5925 uu____5933  in
                   let kwp =
                     let uu____5939 =
                       let uu____5946 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____5946]  in
                     let uu____5947 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5939 uu____5947  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____5952 =
                       let uu____5953 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____5953]  in
                     let uu____5954 =
                       let uu____5955 =
                         let uu____5958 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____5958
                          in
                       let uu____5959 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____5955 uu____5959  in
                     FStar_Syntax_Util.abs uu____5952 uu____5954
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____5975 =
                     should_not_inline_whole_match ||
                       (let uu____5977 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____5977)
                      in
                   if uu____5975 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6009  ->
                        fun celse  ->
                          match uu____6009 with
                          | (g,eff_label,uu____6025,cthen) ->
                              let uu____6035 =
                                let uu____6060 =
                                  let uu____6061 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6061
                                   in
                                lift_and_destruct env uu____6060 celse  in
                              (match uu____6035 with
                               | ((md,uu____6063,uu____6064),(uu____6065,uu____6066,wp_then),
                                  (uu____6068,uu____6069,wp_else)) ->
                                   let uu____6089 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6089 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6102::[] -> comp
                 | uu____6139 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6156 = destruct_comp comp1  in
                     (match uu____6156 with
                      | (uu____6163,uu____6164,wp) ->
                          let wp1 =
                            let uu____6169 =
                              let uu____6170 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6171 =
                                let uu____6172 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6173 =
                                  let uu____6176 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6176]  in
                                uu____6172 :: uu____6173  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6170
                                uu____6171
                               in
                            uu____6169 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____6203 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6203 with
          | FStar_Pervasives_Native.None  ->
              let uu____6212 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6217 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6212 uu____6217
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
            let uu____6250 =
              let uu____6251 = FStar_Syntax_Subst.compress t2  in
              uu____6251.FStar_Syntax_Syntax.n  in
            match uu____6250 with
            | FStar_Syntax_Syntax.Tm_type uu____6254 -> true
            | uu____6255 -> false  in
          let uu____6256 =
            let uu____6257 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6257.FStar_Syntax_Syntax.n  in
          match uu____6256 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6265 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____6275 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____6275
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6277 =
                  let uu____6278 =
                    let uu____6279 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6279
                     in
                  (FStar_Pervasives_Native.None, uu____6278)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6277
                 in
              let e1 =
                let uu____6289 =
                  let uu____6290 =
                    let uu____6291 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6291]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6290  in
                uu____6289 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6296 -> (e, lc)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____6325 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6325 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6348 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6370 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6370, false)
            else
              (let uu____6376 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6376, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6387) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6396 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6396 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___109_6410 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___109_6410.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___109_6410.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___109_6410.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6415 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6415 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___110_6423 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___110_6423.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___110_6423.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___110_6423.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___111_6426 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___111_6426.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___111_6426.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___111_6426.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6430 =
                     let uu____6431 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6431
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6434 =
                          let uu____6435 = FStar_Syntax_Subst.compress f1  in
                          uu____6435.FStar_Syntax_Syntax.n  in
                        match uu____6434 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6438,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6440;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6441;_},uu____6442)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___112_6464 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___112_6464.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___112_6464.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___112_6464.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6465 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____6468 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6468
                              then
                                let uu____6469 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6470 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6471 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6472 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6469 uu____6470 uu____6471 uu____6472
                              else ());
                             (let u_t_opt = comp_univ_opt c  in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let cret = return_value env u_t_opt t xexp  in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____6485 =
                                    let uu____6486 =
                                      let uu____6487 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____6487]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6486
                                     in
                                  uu____6485 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____6491 =
                                let uu____6496 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____6509 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____6510 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____6511 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____6496 uu____6509
                                  e uu____6510 uu____6511
                                 in
                              match uu____6491 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___113_6515 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___113_6515.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___113_6515.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____6517 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____6517
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____6522 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____6522
                                    then
                                      let uu____6523 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6523
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___84_6533  ->
                             match uu___84_6533 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6536 -> []))
                      in
                   let lc1 =
                     let uu____6538 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____6538 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___114_6540 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___114_6540.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___114_6540.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___114_6540.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____6563 =
          let uu____6564 =
            let uu____6565 =
              let uu____6566 =
                let uu____6567 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____6567  in
              [uu____6566]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6565  in
          uu____6564 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____6563  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____6574 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____6574
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6592 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6607 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____6623 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____6623
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6637)::(ens,uu____6639)::uu____6640 ->
                    let uu____6669 =
                      let uu____6672 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____6672  in
                    let uu____6673 =
                      let uu____6674 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____6674  in
                    (uu____6669, uu____6673)
                | uu____6677 ->
                    let uu____6686 =
                      let uu____6691 =
                        let uu____6692 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6692
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6691)
                       in
                    FStar_Errors.raise_error uu____6686
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6708)::uu____6709 ->
                    let uu____6728 =
                      let uu____6733 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6733
                       in
                    (match uu____6728 with
                     | (us_r,uu____6765) ->
                         let uu____6766 =
                           let uu____6771 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6771
                            in
                         (match uu____6766 with
                          | (us_e,uu____6803) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____6806 =
                                  let uu____6807 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____6807
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6806
                                  us_r
                                 in
                              let as_ens =
                                let uu____6809 =
                                  let uu____6810 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____6810
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6809
                                  us_e
                                 in
                              let req =
                                let uu____6814 =
                                  let uu____6815 =
                                    let uu____6816 =
                                      let uu____6827 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6827]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6816
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6815
                                   in
                                uu____6814 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____6845 =
                                  let uu____6846 =
                                    let uu____6847 =
                                      let uu____6858 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6858]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6847
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6846
                                   in
                                uu____6845 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6873 =
                                let uu____6876 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6876  in
                              let uu____6877 =
                                let uu____6878 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6878  in
                              (uu____6873, uu____6877)))
                | uu____6881 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____6907 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6907
       then
         let uu____6908 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6909 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6908 uu____6909
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____6927 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6927
         then
           let uu____6928 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6929 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6928
             uu____6929
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6934 =
      let uu____6935 =
        let uu____6936 = FStar_Syntax_Subst.compress t  in
        uu____6936.FStar_Syntax_Syntax.n  in
      match uu____6935 with
      | FStar_Syntax_Syntax.Tm_app uu____6939 -> false
      | uu____6954 -> true  in
    if uu____6934
    then t
    else
      (let uu____6956 = FStar_Syntax_Util.head_and_args t  in
       match uu____6956 with
       | (head1,args) ->
           let uu____6993 =
             let uu____6994 =
               let uu____6995 = FStar_Syntax_Subst.compress head1  in
               uu____6995.FStar_Syntax_Syntax.n  in
             match uu____6994 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6998 -> false  in
           if uu____6993
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7020 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____7057 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7057 with
             | (formals,uu____7071) ->
                 let n_implicits =
                   let uu____7089 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7165  ->
                             match uu____7165 with
                             | (uu____7172,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7089 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7303 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7303 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7327 =
                     let uu____7332 =
                       let uu____7333 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7340 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7341 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7333 uu____7340 uu____7341
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7332)
                      in
                   let uu____7348 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7327 uu____7348
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___85_7369 =
             match uu___85_7369 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7399 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7399 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7508) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7551,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____7584 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____7584 with
                           | (v1,uu____7624,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____7641 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____7641 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7734 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7734)))
                      | (uu____7761,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____7807 =
                      let uu____7834 = inst_n_binders t  in
                      aux [] uu____7834 bs1  in
                    (match uu____7807 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7905) -> (e, torig, guard)
                          | (uu____7936,[]) when
                              let uu____7967 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____7967 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7968 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8000 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8015 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8023 =
      let uu____8026 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8026
        (FStar_List.map
           (fun u  ->
              let uu____8036 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8036 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8023 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8053 = FStar_Util.set_is_empty x  in
      if uu____8053
      then []
      else
        (let s =
           let uu____8060 =
             let uu____8063 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8063  in
           FStar_All.pipe_right uu____8060 FStar_Util.set_elements  in
         (let uu____8071 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____8071
          then
            let uu____8072 =
              let uu____8073 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____8073  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8072
          else ());
         (let r =
            let uu____8080 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____8080  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____8095 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8095
                     then
                       let uu____8096 =
                         let uu____8097 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8097
                          in
                       let uu____8098 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8099 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8096 uu____8098 uu____8099
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____8121 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____8121 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____8153) -> generalized_univ_names
        | (uu____8160,[]) -> explicit_univ_names
        | uu____8167 ->
            let uu____8176 =
              let uu____8181 =
                let uu____8182 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8182
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8181)
               in
            FStar_Errors.raise_error uu____8176 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____8196 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____8196
       then
         let uu____8197 = FStar_Syntax_Print.term_to_string t  in
         let uu____8198 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____8197 uu____8198
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____8204 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8204
        then
          let uu____8205 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____8205
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____8211 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____8211
         then
           let uu____8212 = FStar_Syntax_Print.term_to_string t  in
           let uu____8213 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____8212 uu____8213
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____8283 =
          let uu____8284 =
            FStar_Util.for_all
              (fun uu____8297  ->
                 match uu____8297 with
                 | (uu____8306,uu____8307,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8284  in
        if uu____8283
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8353 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8353
              then
                let uu____8354 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8354
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.NoDeltaSteps] env c
                 in
              (let uu____8358 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8358
               then
                 let uu____8359 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8359
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8420 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8420 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8550 =
             match uu____8550 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____8616 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8616
                   then
                     let uu____8617 =
                       let uu____8618 =
                         let uu____8621 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8621
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8618
                         (FStar_String.concat ", ")
                        in
                     let uu____8648 =
                       let uu____8649 =
                         let uu____8652 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8652
                           (FStar_List.map
                              (fun uu____8680  ->
                                 match uu____8680 with
                                 | (u,t2) ->
                                     let uu____8687 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____8688 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8687 uu____8688))
                          in
                       FStar_All.pipe_right uu____8649
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8617
                       uu____8648
                   else ());
                  (let univs2 =
                     let uu____8695 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8718  ->
                            match uu____8718 with
                            | (uu____8727,t2) ->
                                let uu____8729 = FStar_Syntax_Free.univs t2
                                   in
                                FStar_Util.set_union univs2 uu____8729)
                       univs1 uu____8695
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8752 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8752
                    then
                      let uu____8753 =
                        let uu____8754 =
                          let uu____8757 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8757
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8754
                          (FStar_String.concat ", ")
                         in
                      let uu____8784 =
                        let uu____8785 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8817  ->
                                  match uu____8817 with
                                  | (u,t2) ->
                                      let uu____8824 =
                                        FStar_Syntax_Print.uvar_to_string u
                                         in
                                      let uu____8825 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2
                                         in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8824 uu____8825))
                           in
                        FStar_All.pipe_right uu____8785
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8753
                        uu____8784
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8855 =
             let uu____8888 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8888  in
           match uu____8855 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9006 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9006
                 then ()
                 else
                   (let uu____9008 = lec_hd  in
                    match uu____9008 with
                    | (lb1,uu____9016,uu____9017) ->
                        let uu____9018 = lec2  in
                        (match uu____9018 with
                         | (lb2,uu____9026,uu____9027) ->
                             let msg =
                               let uu____9029 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9030 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9029 uu____9030
                                in
                             let uu____9031 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9031))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9142  ->
                           match uu____9142 with
                           | (u,uu____9150) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9172  ->
                                       match uu____9172 with
                                       | (u',uu____9180) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9185 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9185
                 then ()
                 else
                   (let uu____9187 = lec_hd  in
                    match uu____9187 with
                    | (lb1,uu____9195,uu____9196) ->
                        let uu____9197 = lec2  in
                        (match uu____9197 with
                         | (lb2,uu____9205,uu____9206) ->
                             let msg =
                               let uu____9208 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9209 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9208 uu____9209
                                in
                             let uu____9210 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9210))
                  in
               let lecs1 =
                 let uu____9220 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9279 = univs_and_uvars_of_lec this_lec  in
                        match uu____9279 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9220 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____9432 = lec_hd  in
                   match uu____9432 with
                   | (lbname,e,c) ->
                       let uu____9442 =
                         let uu____9447 =
                           let uu____9448 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____9449 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____9450 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9448 uu____9449 uu____9450
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9447)
                          in
                       let uu____9451 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9442 uu____9451
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9481  ->
                         match uu____9481 with
                         | (u,k) ->
                             let uu____9494 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____9494 with
                              | FStar_Pervasives_Native.Some uu____9503 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9510 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____9514 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____9514 with
                                   | (bs,kres) ->
                                       ((let uu____9552 =
                                           let uu____9553 =
                                             let uu____9556 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____9556
                                              in
                                           uu____9553.FStar_Syntax_Syntax.n
                                            in
                                         match uu____9552 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9557 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____9561 =
                                               let uu____9562 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____9562
                                                in
                                             if uu____9561
                                             then fail1 kres
                                             else ()
                                         | uu____9564 -> fail1 kres);
                                        (let a =
                                           let uu____9566 =
                                             let uu____9569 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9569
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9566 kres
                                            in
                                         let t =
                                           let uu____9573 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Util.abs bs
                                             uu____9573
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.residual_tot
                                                   kres))
                                            in
                                         FStar_Syntax_Util.set_uvar u t;
                                         (a,
                                           (FStar_Pervasives_Native.Some
                                              FStar_Syntax_Syntax.imp_tag))))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9692  ->
                         match uu____9692 with
                         | (lbname,e,c) ->
                             let uu____9738 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9807 ->
                                   let uu____9822 = (e, c)  in
                                   (match uu____9822 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____9859  ->
                                                   match uu____9859 with
                                                   | (x,uu____9867) ->
                                                       let uu____9872 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9872)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9882 =
                                                let uu____9883 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9883
                                                 in
                                              if uu____9882
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____9891 =
                                            let uu____9892 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9892.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9891 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9915 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9915 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9930 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9932 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9932, gen_tvars))
                                in
                             (match uu____9738 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____10078 = Obj.magic ()  in ());
        (let uu____10080 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10080
         then
           let uu____10081 =
             let uu____10082 =
               FStar_List.map
                 (fun uu____10095  ->
                    match uu____10095 with
                    | (lb,uu____10103,uu____10104) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10082 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10081
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10125  ->
                match uu____10125 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10154 = gen env is_rec lecs  in
           match uu____10154 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10253  ->
                       match uu____10253 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10315 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10315
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10359  ->
                           match uu____10359 with
                           | (l,us,e,c,gvs) ->
                               let uu____10393 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____10394 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____10395 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____10396 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____10397 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10393 uu____10394 uu____10395
                                 uu____10396 uu____10397))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10438  ->
                match uu____10438 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10482 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____10482, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____10525 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____10525 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10531 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10531)
             in
          let is_var e1 =
            let uu____10538 =
              let uu____10539 = FStar_Syntax_Subst.compress e1  in
              uu____10539.FStar_Syntax_Syntax.n  in
            match uu____10538 with
            | FStar_Syntax_Syntax.Tm_name uu____10542 -> true
            | uu____10543 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___115_10559 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___115_10559.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___115_10559.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10560 -> e2  in
          let env2 =
            let uu___116_10562 = env1  in
            let uu____10563 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_10562.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_10562.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_10562.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_10562.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_10562.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_10562.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_10562.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_10562.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_10562.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_10562.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_10562.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_10562.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_10562.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___116_10562.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_10562.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10563;
              FStar_TypeChecker_Env.is_iface =
                (uu___116_10562.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_10562.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_10562.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_10562.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___116_10562.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___116_10562.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___116_10562.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___116_10562.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_10562.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___116_10562.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_10562.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___116_10562.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___116_10562.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___116_10562.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___116_10562.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___116_10562.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___116_10562.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___116_10562.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___116_10562.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___116_10562.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____10564 = check1 env2 t1 t2  in
          match uu____10564 with
          | FStar_Pervasives_Native.None  ->
              let uu____10571 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____10576 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____10571 uu____10576
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10583 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10583
                then
                  let uu____10584 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10584
                else ());
               (let uu____10586 = decorate e t2  in (uu____10586, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____10614 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____10614
        then
          let uu____10619 = discharge g1  in
          let uu____10620 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____10619, uu____10620)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm]  in
           let c1 =
             let uu____10627 =
               let uu____10628 =
                 let uu____10629 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____10629 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____10628
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____10627
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____10631 = destruct_comp c1  in
           match uu____10631 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10648 = FStar_TypeChecker_Env.get_range env  in
                 let uu____10649 =
                   let uu____10650 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____10651 =
                     let uu____10652 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____10653 =
                       let uu____10656 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____10656]  in
                     uu____10652 :: uu____10653  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10650 uu____10651  in
                 uu____10649 FStar_Pervasives_Native.None uu____10648  in
               ((let uu____10660 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____10660
                 then
                   let uu____10661 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10661
                 else ());
                (let g2 =
                   let uu____10664 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10664  in
                 let uu____10665 = discharge g2  in
                 let uu____10666 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____10665, uu____10666))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___86_10690 =
        match uu___86_10690 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10698)::[] -> f fst1
        | uu____10715 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10720 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10720
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44)
         in
      let op_or_e e =
        let uu____10729 =
          let uu____10732 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10732  in
        FStar_All.pipe_right uu____10729
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46)
         in
      let op_or_t t =
        let uu____10743 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10743
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
         in
      let short_op_ite uu___87_10757 =
        match uu___87_10757 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10765)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10784)::[] ->
            let uu____10813 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10813
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10818 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10828 =
          let uu____10835 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10835)  in
        let uu____10840 =
          let uu____10849 =
            let uu____10856 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10856)  in
          let uu____10861 =
            let uu____10870 =
              let uu____10877 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10877)  in
            let uu____10882 =
              let uu____10891 =
                let uu____10898 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10898)  in
              let uu____10903 =
                let uu____10912 =
                  let uu____10919 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10919)  in
                [uu____10912; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10891 :: uu____10903  in
            uu____10870 :: uu____10882  in
          uu____10849 :: uu____10861  in
        uu____10828 :: uu____10840  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10970 =
            FStar_Util.find_map table
              (fun uu____10984  ->
                 match uu____10984 with
                 | (x,mk1) ->
                     let uu____10999 = FStar_Ident.lid_equals x lid  in
                     if uu____10999
                     then
                       let uu____11002 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11002
                     else FStar_Pervasives_Native.None)
             in
          (match uu____10970 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11005 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11009 =
      let uu____11010 = FStar_Syntax_Util.un_uinst l  in
      uu____11010.FStar_Syntax_Syntax.n  in
    match uu____11009 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11014 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11038)::uu____11039 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11050 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11057,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11058))::uu____11059 -> bs
      | uu____11076 ->
          let uu____11077 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11077 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11081 =
                 let uu____11082 = FStar_Syntax_Subst.compress t  in
                 uu____11082.FStar_Syntax_Syntax.n  in
               (match uu____11081 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11086) ->
                    let uu____11103 =
                      FStar_Util.prefix_until
                        (fun uu___88_11143  ->
                           match uu___88_11143 with
                           | (uu____11150,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11151)) ->
                               false
                           | uu____11154 -> true) bs'
                       in
                    (match uu____11103 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11189,uu____11190) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11262,uu____11263) ->
                         let uu____11336 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11354  ->
                                   match uu____11354 with
                                   | (x,uu____11362) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____11336
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11409  ->
                                     match uu____11409 with
                                     | (x,i) ->
                                         let uu____11428 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11428, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11438 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            let uu____11456 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____11456
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____11471 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11471
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____11494 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11494
         then
           ((let uu____11496 = FStar_Ident.text_of_lid lident  in
             d uu____11496);
            (let uu____11497 = FStar_Ident.text_of_lid lident  in
             let uu____11498 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____11497 uu____11498))
         else ());
        (let fv =
           let uu____11501 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11501
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____11511 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___117_11517 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___117_11517.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___117_11517.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___117_11517.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___117_11517.FStar_Syntax_Syntax.sigattrs)
           }), uu____11511))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      let visibility uu___89_11527 =
        match uu___89_11527 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11528 -> false  in
      let reducibility uu___90_11532 =
        match uu___90_11532 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11533 -> false  in
      let assumption uu___91_11537 =
        match uu___91_11537 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11538 -> false  in
      let reification uu___92_11542 =
        match uu___92_11542 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11543 -> true
        | uu____11544 -> false  in
      let inferred uu___93_11548 =
        match uu___93_11548 with
        | FStar_Syntax_Syntax.Discriminator uu____11549 -> true
        | FStar_Syntax_Syntax.Projector uu____11550 -> true
        | FStar_Syntax_Syntax.RecordType uu____11555 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11564 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11573 -> false  in
      let has_eq uu___94_11577 =
        match uu___94_11577 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11578 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____11638 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11643 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____11647 =
        let uu____11648 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___95_11652  ->
                  match uu___95_11652 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11653 -> false))
           in
        FStar_All.pipe_right uu____11648 Prims.op_Negation  in
      if uu____11647
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11666 =
            let uu____11671 =
              let uu____11672 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11672 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11671)  in
          FStar_Errors.raise_error uu____11666 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11680 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11684 =
            let uu____11685 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11685  in
          if uu____11684 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11690),uu____11691) ->
              ((let uu____11707 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11707
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11711 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11711
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11717 ->
              let uu____11726 =
                let uu____11727 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____11727  in
              if uu____11726 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11733 ->
              let uu____11740 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11740 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11744 ->
              let uu____11751 =
                let uu____11752 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11752  in
              if uu____11751 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11758 ->
              let uu____11759 =
                let uu____11760 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11760  in
              if uu____11759 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11766 ->
              let uu____11767 =
                let uu____11768 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11768  in
              if uu____11767 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11774 ->
              let uu____11787 =
                let uu____11788 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11788  in
              if uu____11787 then err'1 () else ()
          | uu____11794 -> ()))
      else ()
  