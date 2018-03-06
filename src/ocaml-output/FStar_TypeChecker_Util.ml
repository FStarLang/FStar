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
  fun uu___80_93  ->
    match uu___80_93 with
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
                     let uu___104_257 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u  in
                         (reason, env, uu____286, t, k, r)  in
                       [uu____273]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___104_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___104_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___104_257.FStar_TypeChecker_Env.univ_ineqs);
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
          FStar_Syntax_Syntax.lbattrs = uu____423;_} ->
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
                   let uu____472 =
                     let uu____473 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____473.FStar_Syntax_Syntax.n  in
                   match uu____472 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____480 = FStar_Syntax_Util.type_u ()  in
                       (match uu____480 with
                        | (k,uu____490) ->
                            let t2 =
                              let uu____492 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____492
                                FStar_Pervasives_Native.fst
                               in
                            ((let uu___105_502 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___105_502.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___105_502.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____503 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____540) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____547) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____610) ->
                       let uu____631 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____691  ->
                                 fun uu____692  ->
                                   match (uu____691, uu____692) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____770 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____770 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____631 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____882 = aux must_check_ty1 scope body  in
                            (match uu____882 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____911 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____911
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____918 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____918
                                   then
                                     let uu____919 =
                                       FStar_Range.string_of_range r  in
                                     let uu____920 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____921 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____919 uu____920 uu____921
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____931 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____945 =
                            let uu____950 =
                              let uu____951 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____951
                                FStar_Pervasives_Native.fst
                               in
                            FStar_Util.Inl uu____950  in
                          (uu____945, false))
                    in
                 let uu____964 =
                   let uu____973 = t_binders env  in aux false uu____973 e
                    in
                 match uu____964 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____998 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____998
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1002 =
                                let uu____1007 =
                                  let uu____1008 =
                                    FStar_Syntax_Print.comp_to_string c  in
                                  FStar_Util.format1
                                    "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                    uu____1008
                                   in
                                (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                  uu____1007)
                                 in
                              FStar_Errors.raise_error uu____1002 rng)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____1016 ->
               let uu____1017 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1017 with
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
            let uu____1097 =
              let uu____1102 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1102 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1107;
                  FStar_Syntax_Syntax.vars = uu____1108;_} ->
                  let uu____1111 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1111 with
                   | (t,uu____1121) ->
                       let uu____1122 = new_uvar env1 t  in
                       (uu____1122, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1097 with
            | (t_x,guard) ->
                ((let uu___106_1131 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___106_1131.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___106_1131.FStar_Syntax_Syntax.index);
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
                  | uu____1200 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1208) ->
                let uu____1213 = FStar_Syntax_Util.type_u ()  in
                (match uu____1213 with
                 | (k,uu____1239) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___107_1242 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___107_1242.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___107_1242.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1243 =
                       let uu____1248 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1248 t
                        in
                     (match uu____1243 with
                      | (e,u) ->
                          let p2 =
                            let uu___108_1274 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___108_1274.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1284 = check_bv env1 x  in
                (match uu____1284 with
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
                let uu____1325 = check_bv env1 x  in
                (match uu____1325 with
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
                let uu____1382 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1518  ->
                          fun uu____1519  ->
                            match (uu____1518, uu____1519) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1717 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1717 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1793 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1793, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1382 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1924 =
                         let uu____1925 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1926 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1925 uu____1926
                          in
                       uu____1924 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1933 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1944 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1955 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1933, uu____1944, uu____1955, env2, e, guard,
                       (let uu___109_1977 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___109_1977.FStar_Syntax_Syntax.p)
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
                    (fun uu____2061  ->
                       match uu____2061 with
                       | (p2,imp) ->
                           let uu____2080 = elaborate_pat env1 p2  in
                           (uu____2080, imp)) pats
                   in
                let uu____2085 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2085 with
                 | (uu____2092,t) ->
                     let uu____2094 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2094 with
                      | (f,uu____2110) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2232::uu____2233) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments")
                                  (FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | (uu____2284::uu____2285,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2363  ->
                                        match uu____2363 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2390 =
                                                     let uu____2393 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2393
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2390
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2395 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2395, true)
                                             | uu____2400 ->
                                                 let uu____2403 =
                                                   let uu____2408 =
                                                     let uu____2409 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2409
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2408)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2403
                                                   (FStar_Ident.range_of_lid
                                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2483,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2484)) when p_imp ->
                                     let uu____2487 = aux formals' pats'  in
                                     (p2, true) :: uu____2487
                                 | (uu____2504,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       maybe_dot inaccessible a
                                         (FStar_Ident.range_of_lid
                                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                        in
                                     let uu____2512 = aux formals' pats2  in
                                     (p3, true) :: uu____2512
                                 | (uu____2529,imp) ->
                                     let uu____2535 =
                                       let uu____2542 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2542)  in
                                     let uu____2545 = aux formals' pats'  in
                                     uu____2535 :: uu____2545)
                             in
                          let uu___110_2560 = p1  in
                          let uu____2563 =
                            let uu____2564 =
                              let uu____2577 = aux f pats1  in
                              (fv, uu____2577)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2564  in
                          {
                            FStar_Syntax_Syntax.v = uu____2563;
                            FStar_Syntax_Syntax.p =
                              (uu___110_2560.FStar_Syntax_Syntax.p)
                          }))
            | uu____2594 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2630 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2630 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2688 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2688 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2714 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2714
                       p3.FStar_Syntax_Syntax.p
                 | uu____2737 -> (b, a, w, arg, guard, p3))
             in
          let uu____2746 = one_pat true env p  in
          match uu____2746 with
          | (b,uu____2776,uu____2777,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____2823,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2825)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2830,uu____2831) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2835 =
                    let uu____2836 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2837 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2836 uu____2837
                     in
                  failwith uu____2835)
               else ();
               (let uu____2840 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2840
                then
                  let uu____2841 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2842 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2841
                    uu____2842
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___111_2846 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___111_2846.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___111_2846.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2850 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2850
                then
                  let uu____2851 =
                    let uu____2852 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2853 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2852 uu____2853
                     in
                  failwith uu____2851
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___112_2857 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___112_2857.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___112_2857.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2859),uu____2860) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2882 =
                  let uu____2883 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2883  in
                if uu____2882
                then
                  let uu____2884 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2884
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2903;
                FStar_Syntax_Syntax.vars = uu____2904;_},args))
              ->
              ((let uu____2943 =
                  let uu____2944 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2944 Prims.op_Negation  in
                if uu____2943
                then
                  let uu____2945 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2945
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3081)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3156) ->
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
                       | ((e2,imp),uu____3193) ->
                           let pat =
                             let uu____3215 = aux argpat e2  in
                             let uu____3216 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3215, uu____3216)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3221 ->
                      let uu____3244 =
                        let uu____3245 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3246 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3245 uu____3246
                         in
                      failwith uu____3244
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3258;
                     FStar_Syntax_Syntax.vars = uu____3259;_},uu____3260);
                FStar_Syntax_Syntax.pos = uu____3261;
                FStar_Syntax_Syntax.vars = uu____3262;_},args))
              ->
              ((let uu____3305 =
                  let uu____3306 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3306 Prims.op_Negation  in
                if uu____3305
                then
                  let uu____3307 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3307
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3443)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3518) ->
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
                       | ((e2,imp),uu____3555) ->
                           let pat =
                             let uu____3577 = aux argpat e2  in
                             let uu____3578 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3577, uu____3578)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3583 ->
                      let uu____3606 =
                        let uu____3607 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3608 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3607 uu____3608
                         in
                      failwith uu____3606
                   in
                match_args [] args argpats))
          | uu____3617 ->
              let uu____3622 =
                let uu____3623 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3624 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3625 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3623 uu____3624 uu____3625
                 in
              failwith uu____3622
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
    let pat_as_arg uu____3662 =
      match uu____3662 with
      | (p,i) ->
          let uu____3679 = decorated_pattern_as_term p  in
          (match uu____3679 with
           | (vars,te) ->
               let uu____3702 =
                 let uu____3707 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3707)  in
               (vars, uu____3702))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3721 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3721)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3725 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3725)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3729 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3729)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3750 =
          let uu____3765 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3765 FStar_List.unzip  in
        (match uu____3750 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3875 =
               let uu____3876 =
                 let uu____3877 =
                   let uu____3892 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3892, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3877  in
               mk1 uu____3876  in
             (vars1, uu____3875))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3922,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3932,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3946 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3970)::[] -> wp
      | uu____3987 ->
          let uu____3996 =
            let uu____3997 =
              let uu____3998 =
                FStar_List.map
                  (fun uu____4008  ->
                     match uu____4008 with
                     | (x,uu____4014) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____3998 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3997
             in
          failwith uu____3996
       in
    let uu____4019 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4019, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4033 = destruct_comp c  in
        match uu____4033 with
        | (u,uu____4041,wp) ->
            let uu____4043 =
              let uu____4052 =
                let uu____4053 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4053  in
              [uu____4052]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4043;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4063 =
          let uu____4070 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4071 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4070 uu____4071  in
        match uu____4063 with | (m,uu____4073,uu____4074) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4084 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4084
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
        let uu____4121 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4121 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4158 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4158 with
             | (a,kwp) ->
                 let uu____4189 = destruct_comp m1  in
                 let uu____4196 = destruct_comp m2  in
                 ((md, a, kwp), uu____4189, uu____4196))
  
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
            let uu____4258 =
              let uu____4259 =
                let uu____4268 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4268]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4259;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4258
  
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
          if FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
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
      let uu____4307 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4307
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4310  ->
           let uu____4311 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4311)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4315 =
      let uu____4316 = FStar_Syntax_Subst.compress t  in
      uu____4316.FStar_Syntax_Syntax.n  in
    match uu____4315 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4319 -> true
    | uu____4332 -> false
  
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
              let uu____4370 =
                let uu____4371 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4371  in
              if uu____4370
              then f
              else (let uu____4373 = reason1 ()  in label uu____4373 r f)
  
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
            let uu___113_4384 = g  in
            let uu____4385 =
              let uu____4386 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4386  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4385;
              FStar_TypeChecker_Env.deferred =
                (uu___113_4384.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___113_4384.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___113_4384.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4400 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4400
        then c
        else
          (let uu____4402 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4402
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4441 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4441]  in
                       let us =
                         let uu____4445 =
                           let uu____4448 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4448]  in
                         u_res :: uu____4445  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4452 =
                         let uu____4453 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4454 =
                           let uu____4455 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4456 =
                             let uu____4459 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4460 =
                               let uu____4463 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4463]  in
                             uu____4459 :: uu____4460  in
                           uu____4455 :: uu____4456  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4453 uu____4454
                          in
                       uu____4452 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4467 = destruct_comp c1  in
              match uu____4467 with
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
          (fun uu____4494  ->
             let uu____4495 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4495)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___81_4502  ->
            match uu___81_4502 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4503 -> false))
  
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
                (let uu____4519 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4519))
               &&
               (let uu____4526 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4526 with
                | (head1,uu____4540) ->
                    let uu____4557 =
                      let uu____4558 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4558.FStar_Syntax_Syntax.n  in
                    (match uu____4557 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4562 =
                           let uu____4563 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4563
                            in
                         Prims.op_Negation uu____4562
                     | uu____4564 -> true)))
              &&
              (let uu____4566 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4566)
  
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
            let uu____4584 =
              let uu____4585 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4585  in
            if uu____4584
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4587 = FStar_Syntax_Util.is_unit t  in
               if uu____4587
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
                    let uu____4593 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4593
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4595 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4595 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4603 =
                             let uu____4604 =
                               let uu____4605 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4606 =
                                 let uu____4607 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4608 =
                                   let uu____4611 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4611]  in
                                 uu____4607 :: uu____4608  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4605
                                 uu____4606
                                in
                             uu____4604 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4603)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4615 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4615
           then
             let uu____4616 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4617 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4618 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4616 uu____4617 uu____4618
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4629 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___82_4633  ->
              match uu___82_4633 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4634 -> false))
       in
    if uu____4629
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___83_4643  ->
              match uu___83_4643 with
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
        let uu____4656 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4656
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4659 = destruct_comp c1  in
           match uu____4659 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4673 =
                   let uu____4674 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4675 =
                     let uu____4676 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4677 =
                       let uu____4680 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4681 =
                         let uu____4684 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4684]  in
                       uu____4680 :: uu____4681  in
                     uu____4676 :: uu____4677  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4674 uu____4675  in
                 uu____4673 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4687 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4687)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4702 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4704 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4704
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4707 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4707 weaken
  
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
               let uu____4740 = destruct_comp c1  in
               match uu____4740 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____4754 =
                       let uu____4755 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____4756 =
                         let uu____4757 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____4758 =
                           let uu____4761 =
                             let uu____4762 =
                               let uu____4763 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____4763 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____4762
                              in
                           let uu____4764 =
                             let uu____4767 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____4767]  in
                           uu____4761 :: uu____4764  in
                         uu____4757 :: uu____4758  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4755 uu____4756
                        in
                     uu____4754 FStar_Pervasives_Native.None
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
            let uu____4802 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____4802
            then (lc, g0)
            else
              (let flags1 =
                 let uu____4811 =
                   let uu____4818 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____4818
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4811 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____4838 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___84_4846  ->
                               match uu___84_4846 with
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
                               | uu____4849 -> []))
                        in
                     FStar_List.append flags1 uu____4838
                  in
               let strengthen uu____4853 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____4857 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____4857 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____4860 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4860
                          then
                            let uu____4861 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____4862 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____4861 uu____4862
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____4864 =
                 let uu____4865 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____4865
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____4864,
                 (let uu___114_4867 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___114_4867.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___114_4867.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___114_4867.FStar_TypeChecker_Env.implicits)
                  })))
  
let (stable_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Syntax_Util.is_tac_lcomp lc)
  
let (stable_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Syntax_Util.is_tot_or_gtot_comp c) ||
      (FStar_Syntax_Util.is_tac_comp c)
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (stable_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___85_4882  ->
            match uu___85_4882 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4883 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____4900 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4900
          then e
          else
            (let uu____4902 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4904 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4904)
                in
             if uu____4902
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
          fun uu____4942  ->
            match uu____4942 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4960 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4960 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4968 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4968
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4975 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____4975
                       then
                         let uu____4978 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____4978
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4982 = stable_lcomp lc21  in
                             if uu____4982
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4987 =
                            (stable_lcomp lc11) && (stable_lcomp lc21)  in
                          if uu____4987
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____4991 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____4991
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____4998 =
                  let uu____4999 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____4999
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
                       (fun uu____5013  ->
                          let uu____5014 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5015 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5017 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5014 uu____5015 uu____5017);
                     (let aux uu____5029 =
                        let uu____5030 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5030
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5051 ->
                              let uu____5052 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5052
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5071 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5071
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5138 =
                              let uu____5143 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5143, reason)  in
                            FStar_Util.Inl uu____5138
                        | uu____5150 -> aux ()  in
                      let try_simplify uu____5172 =
                        let rec maybe_close t x c =
                          let uu____5183 =
                            let uu____5184 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5184.FStar_Syntax_Syntax.n  in
                          match uu____5183 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5188) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5194 -> c  in
                        let uu____5195 =
                          let uu____5196 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5196  in
                        if uu____5195
                        then
                          let uu____5207 =
                            (stable_comp c1) && (stable_comp c2)  in
                          (if uu____5207
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5221 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5221))
                        else
                          (let uu____5231 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5231
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5241 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5241
                              then
                                let uu____5250 =
                                  let uu____5255 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5255, "both gtot")  in
                                FStar_Util.Inl uu____5250
                              else
                                (let uu____5261 =
                                   (stable_comp c1) && (stable_comp c2)  in
                                 if uu____5261
                                 then
                                   let ty = FStar_Syntax_Util.comp_result c2
                                      in
                                   let uu____5273 =
                                     let uu____5278 =
                                       let uu____5279 =
                                         let uu____5280 =
                                           let uu____5281 =
                                             env.FStar_TypeChecker_Env.universe_of
                                               env ty
                                              in
                                           [uu____5281]  in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             uu____5280;
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Tac_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             ty;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags =
                                             [FStar_Syntax_Syntax.SOMETRIVIAL;
                                             FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____5279
                                        in
                                     (uu____5278, "both Tac")  in
                                   FStar_Util.Inl uu____5273
                                 else
                                   (match (e1opt, b) with
                                    | (FStar_Pervasives_Native.Some
                                       e,FStar_Pervasives_Native.Some x) ->
                                        let uu____5311 =
                                          (FStar_Syntax_Util.is_total_comp c1)
                                            &&
                                            (let uu____5313 =
                                               FStar_Syntax_Syntax.is_null_bv
                                                 x
                                                in
                                             Prims.op_Negation uu____5313)
                                           in
                                        if uu____5311
                                        then
                                          let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e)]
                                              c2
                                             in
                                          let x1 =
                                            let uu___115_5324 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_5324.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_5324.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                            }  in
                                          let uu____5325 =
                                            let uu____5330 =
                                              maybe_close
                                                x1.FStar_Syntax_Syntax.sort
                                                x1 c21
                                               in
                                            (uu____5330, "c1 Tot")  in
                                          FStar_Util.Inl uu____5325
                                        else aux ()
                                    | uu____5336 -> aux ()))))
                         in
                      let uu____5345 = try_simplify ()  in
                      match uu____5345 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5365  ->
                                let uu____5366 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5366);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5375  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5390 = lift_and_destruct env c11 c21
                                 in
                              match uu____5390 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5447 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5447]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5449 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5449]
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
                                    let uu____5462 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5463 =
                                      let uu____5466 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5467 =
                                        let uu____5470 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5471 =
                                          let uu____5474 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5475 =
                                            let uu____5478 =
                                              let uu____5479 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5479
                                               in
                                            [uu____5478]  in
                                          uu____5474 :: uu____5475  in
                                        uu____5470 :: uu____5471  in
                                      uu____5466 :: uu____5467  in
                                    uu____5462 :: uu____5463  in
                                  let wp =
                                    let uu____5483 =
                                      let uu____5484 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5484 wp_args
                                       in
                                    uu____5483 FStar_Pervasives_Native.None
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
                              let uu____5503 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5503 with
                              | (m,uu____5511,lift2) ->
                                  let c23 =
                                    let uu____5514 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5514
                                     in
                                  let uu____5515 = destruct_comp c12  in
                                  (match uu____5515 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5529 =
                                           let uu____5530 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____5531 =
                                             let uu____5532 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____5533 =
                                               let uu____5536 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____5536]  in
                                             uu____5532 :: uu____5533  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5530 uu____5531
                                            in
                                         uu____5529
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
                            let uu____5542 = destruct_comp c1_typ  in
                            match uu____5542 with
                            | (u_res_t1,res_t1,uu____5551) ->
                                let uu____5552 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____5552
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____5555 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____5555
                                   then
                                     (debug1
                                        (fun uu____5563  ->
                                           let uu____5564 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____5565 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5564 uu____5565);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5568 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5570 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____5570)
                                         in
                                      if uu____5568
                                      then
                                        let e1' =
                                          let uu____5592 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____5592
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____5603  ->
                                              let uu____5604 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____5605 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5604 uu____5605);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5617  ->
                                              let uu____5618 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5619 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5618 uu____5619);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____5622 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5622
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
      | uu____5634 -> g2
  
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
            (let uu____5650 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____5650)
           in
        let flags1 =
          if should_return1
          then
            let uu____5656 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____5656
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____5664 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____5668 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____5668
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____5670 =
              let uu____5671 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____5671  in
            (if uu____5670
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___116_5674 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___116_5674.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___116_5674.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___116_5674.FStar_Syntax_Syntax.effect_args);
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
               let uu____5685 =
                 let uu____5688 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____5688
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5685
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____5693 =
               let uu____5694 =
                 let uu____5695 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5695
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____5694  in
             FStar_Syntax_Util.comp_set_flags uu____5693 flags1)
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
            fun uu____5718  ->
              match uu____5718 with
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
                    let uu____5730 =
                      ((let uu____5733 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5733) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5730
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5743 =
        let uu____5744 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5744  in
      FStar_Syntax_Syntax.fvar uu____5743 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5803  ->
                 match uu____5803 with
                 | (uu____5816,eff_label,uu____5818,uu____5819) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____5828 =
          let uu____5835 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5867  ->
                    match uu____5867 with
                    | (uu____5880,uu____5881,flags1,uu____5883) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___86_5895  ->
                                match uu___86_5895 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5896 -> false))))
             in
          if uu____5835
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____5828 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5917 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____5919 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5919
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5939 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____5940 =
                     let uu____5941 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____5942 =
                       let uu____5943 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____5944 =
                         let uu____5947 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____5948 =
                           let uu____5951 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____5952 =
                             let uu____5955 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____5955]  in
                           uu____5951 :: uu____5952  in
                         uu____5947 :: uu____5948  in
                       uu____5943 :: uu____5944  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5941 uu____5942  in
                   uu____5940 FStar_Pervasives_Native.None uu____5939  in
                 let default_case =
                   let post_k =
                     let uu____5962 =
                       let uu____5969 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____5969]  in
                     let uu____5970 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5962 uu____5970  in
                   let kwp =
                     let uu____5976 =
                       let uu____5983 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____5983]  in
                     let uu____5984 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5976 uu____5984  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____5989 =
                       let uu____5990 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____5990]  in
                     let uu____5991 =
                       let uu____5992 =
                         let uu____5995 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____5995
                          in
                       let uu____5996 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____5992 uu____5996  in
                     FStar_Syntax_Util.abs uu____5989 uu____5991
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
                   let uu____6012 =
                     should_not_inline_whole_match ||
                       (let uu____6014 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6014)
                      in
                   if uu____6012 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6046  ->
                        fun celse  ->
                          match uu____6046 with
                          | (g,eff_label,uu____6062,cthen) ->
                              let uu____6072 =
                                let uu____6097 =
                                  let uu____6098 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6098
                                   in
                                lift_and_destruct env uu____6097 celse  in
                              (match uu____6072 with
                               | ((md,uu____6100,uu____6101),(uu____6102,uu____6103,wp_then),
                                  (uu____6105,uu____6106,wp_else)) ->
                                   let uu____6126 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6126 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6139::[] -> comp
                 | uu____6176 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6193 = destruct_comp comp1  in
                     (match uu____6193 with
                      | (uu____6200,uu____6201,wp) ->
                          let wp1 =
                            let uu____6206 =
                              let uu____6207 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6208 =
                                let uu____6209 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6210 =
                                  let uu____6213 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6213]  in
                                uu____6209 :: uu____6210  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6207
                                uu____6208
                               in
                            uu____6206 FStar_Pervasives_Native.None
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
          let uu____6240 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6240 with
          | FStar_Pervasives_Native.None  ->
              let uu____6249 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6254 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6249 uu____6254
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
            let uu____6287 =
              let uu____6288 = FStar_Syntax_Subst.compress t2  in
              uu____6288.FStar_Syntax_Syntax.n  in
            match uu____6287 with
            | FStar_Syntax_Syntax.Tm_type uu____6291 -> true
            | uu____6292 -> false  in
          let uu____6293 =
            let uu____6294 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6294.FStar_Syntax_Syntax.n  in
          match uu____6293 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6302 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6313 =
                  let uu____6314 =
                    let uu____6315 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6315
                     in
                  (FStar_Pervasives_Native.None, uu____6314)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6313
                 in
              let e1 =
                let uu____6325 =
                  let uu____6326 =
                    let uu____6327 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6327]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6326  in
                uu____6325 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6332 -> (e, lc)
  
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
              (let uu____6361 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6361 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6384 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6406 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6406, false)
            else
              (let uu____6412 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6412, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6423) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6432 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6432 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___117_6446 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___117_6446.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___117_6446.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___117_6446.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6451 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6451 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___118_6459 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___118_6459.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___118_6459.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___118_6459.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___119_6462 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_6462.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_6462.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___119_6462.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6466 =
                     let uu____6467 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6467
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6470 =
                          let uu____6471 = FStar_Syntax_Subst.compress f1  in
                          uu____6471.FStar_Syntax_Syntax.n  in
                        match uu____6470 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6474,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6476;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6477;_},uu____6478)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___120_6500 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___120_6500.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___120_6500.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___120_6500.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6501 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____6504 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6504
                              then
                                let uu____6505 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6506 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6507 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6508 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6505 uu____6506 uu____6507 uu____6508
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
                                  let uu____6521 =
                                    let uu____6522 =
                                      let uu____6523 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____6523]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6522
                                     in
                                  uu____6521 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____6527 =
                                let uu____6532 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____6545 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____6546 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____6547 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____6532 uu____6545
                                  e uu____6546 uu____6547
                                 in
                              match uu____6527 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___121_6551 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_6551.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_6551.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____6553 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____6553
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____6558 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____6558
                                    then
                                      let uu____6559 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6559
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___87_6569  ->
                             match uu___87_6569 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6572 -> []))
                      in
                   let lc1 =
                     let uu____6574 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____6574 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___122_6576 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_6576.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_6576.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___122_6576.FStar_TypeChecker_Env.implicits)
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
        let uu____6599 =
          let uu____6600 =
            let uu____6601 =
              let uu____6602 =
                let uu____6603 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____6603  in
              [uu____6602]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6601  in
          uu____6600 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____6599  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____6610 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____6610
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6628 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6643 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6672)::(ens,uu____6674)::uu____6675 ->
                    let uu____6704 =
                      let uu____6707 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____6707  in
                    let uu____6708 =
                      let uu____6709 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____6709  in
                    (uu____6704, uu____6708)
                | uu____6712 ->
                    let uu____6721 =
                      let uu____6726 =
                        let uu____6727 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6727
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6726)
                       in
                    FStar_Errors.raise_error uu____6721
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6743)::uu____6744 ->
                    let uu____6763 =
                      let uu____6768 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6768
                       in
                    (match uu____6763 with
                     | (us_r,uu____6800) ->
                         let uu____6801 =
                           let uu____6806 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6806
                            in
                         (match uu____6801 with
                          | (us_e,uu____6838) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____6841 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6841
                                  us_r
                                 in
                              let as_ens =
                                let uu____6843 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6843
                                  us_e
                                 in
                              let req =
                                let uu____6847 =
                                  let uu____6848 =
                                    let uu____6849 =
                                      let uu____6860 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6860]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6849
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6848
                                   in
                                uu____6847 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____6878 =
                                  let uu____6879 =
                                    let uu____6880 =
                                      let uu____6891 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6891]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6880
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6879
                                   in
                                uu____6878 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6906 =
                                let uu____6909 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6909  in
                              let uu____6910 =
                                let uu____6911 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6911  in
                              (uu____6906, uu____6910)))
                | uu____6914 -> failwith "Impossible"))
  
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
      (let uu____6940 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6940
       then
         let uu____6941 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6942 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6941 uu____6942
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
        (let uu____6960 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6960
         then
           let uu____6961 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6962 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6961
             uu____6962
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6967 =
      let uu____6968 =
        let uu____6969 = FStar_Syntax_Subst.compress t  in
        uu____6969.FStar_Syntax_Syntax.n  in
      match uu____6968 with
      | FStar_Syntax_Syntax.Tm_app uu____6972 -> false
      | uu____6987 -> true  in
    if uu____6967
    then t
    else
      (let uu____6989 = FStar_Syntax_Util.head_and_args t  in
       match uu____6989 with
       | (head1,args) ->
           let uu____7026 =
             let uu____7027 =
               let uu____7028 = FStar_Syntax_Subst.compress head1  in
               uu____7028.FStar_Syntax_Syntax.n  in
             match uu____7027 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7031 -> false  in
           if uu____7026
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7053 ->
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
             let uu____7090 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7090 with
             | (formals,uu____7104) ->
                 let n_implicits =
                   let uu____7122 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7198  ->
                             match uu____7198 with
                             | (uu____7205,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7122 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7336 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7336 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7360 =
                     let uu____7365 =
                       let uu____7366 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7373 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7374 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7366 uu____7373 uu____7374
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7365)
                      in
                   let uu____7381 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7360 uu____7381
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___88_7402 =
             match uu___88_7402 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7432 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7432 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7541) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7584,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____7617 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____7617 with
                           | (v1,uu____7657,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____7674 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____7674 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7767 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7767)))
                      | (uu____7794,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____7840 =
                      let uu____7867 = inst_n_binders t  in
                      aux [] uu____7867 bs1  in
                    (match uu____7840 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7938) -> (e, torig, guard)
                          | (uu____7969,[]) when
                              let uu____8000 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8000 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8001 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8033 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8048 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8056 =
      let uu____8059 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8059
        (FStar_List.map
           (fun u  ->
              let uu____8069 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8069 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8056 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8086 = FStar_Util.set_is_empty x  in
      if uu____8086
      then []
      else
        (let s =
           let uu____8093 =
             let uu____8096 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8096  in
           FStar_All.pipe_right uu____8093 FStar_Util.set_elements  in
         (let uu____8104 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____8104
          then
            let uu____8105 =
              let uu____8106 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____8106  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8105
          else ());
         (let r =
            let uu____8113 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____8113  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____8128 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8128
                     then
                       let uu____8129 =
                         let uu____8130 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8130
                          in
                       let uu____8131 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8132 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8129 uu____8131 uu____8132
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
        let uu____8154 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____8154 FStar_Util.set_elements  in
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
        | ([],uu____8186) -> generalized_univ_names
        | (uu____8193,[]) -> explicit_univ_names
        | uu____8200 ->
            let uu____8209 =
              let uu____8214 =
                let uu____8215 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8215
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8214)
               in
            FStar_Errors.raise_error uu____8209 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____8229 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____8229
       then
         let uu____8230 = FStar_Syntax_Print.term_to_string t  in
         let uu____8231 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____8230 uu____8231
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____8237 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8237
        then
          let uu____8238 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____8238
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____8244 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____8244
         then
           let uu____8245 = FStar_Syntax_Print.term_to_string t  in
           let uu____8246 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____8245 uu____8246
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
        let uu____8316 =
          let uu____8317 =
            FStar_Util.for_all
              (fun uu____8330  ->
                 match uu____8330 with
                 | (uu____8339,uu____8340,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8317  in
        if uu____8316
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8386 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8386
              then
                let uu____8387 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8387
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.NoDeltaSteps] env c
                 in
              (let uu____8391 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8391
               then
                 let uu____8392 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8392
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8453 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8453 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8583 =
             match uu____8583 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____8649 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8649
                   then
                     let uu____8650 =
                       let uu____8651 =
                         let uu____8654 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8654
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8651
                         (FStar_String.concat ", ")
                        in
                     let uu____8681 =
                       let uu____8682 =
                         let uu____8685 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8685
                           (FStar_List.map
                              (fun uu____8713  ->
                                 match uu____8713 with
                                 | (u,t2) ->
                                     let uu____8720 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____8721 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8720 uu____8721))
                          in
                       FStar_All.pipe_right uu____8682
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8650
                       uu____8681
                   else ());
                  (let univs2 =
                     let uu____8728 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8751  ->
                            match uu____8751 with
                            | (uu____8760,t2) ->
                                let uu____8762 = FStar_Syntax_Free.univs t2
                                   in
                                FStar_Util.set_union univs2 uu____8762)
                       univs1 uu____8728
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8785 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8785
                    then
                      let uu____8786 =
                        let uu____8787 =
                          let uu____8790 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8790
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8787
                          (FStar_String.concat ", ")
                         in
                      let uu____8817 =
                        let uu____8818 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8850  ->
                                  match uu____8850 with
                                  | (u,t2) ->
                                      let uu____8857 =
                                        FStar_Syntax_Print.uvar_to_string u
                                         in
                                      let uu____8858 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2
                                         in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8857 uu____8858))
                           in
                        FStar_All.pipe_right uu____8818
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8786
                        uu____8817
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8888 =
             let uu____8921 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8921  in
           match uu____8888 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9039 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9039
                 then ()
                 else
                   (let uu____9041 = lec_hd  in
                    match uu____9041 with
                    | (lb1,uu____9049,uu____9050) ->
                        let uu____9051 = lec2  in
                        (match uu____9051 with
                         | (lb2,uu____9059,uu____9060) ->
                             let msg =
                               let uu____9062 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9063 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9062 uu____9063
                                in
                             let uu____9064 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9064))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9175  ->
                           match uu____9175 with
                           | (u,uu____9183) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9205  ->
                                       match uu____9205 with
                                       | (u',uu____9213) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9218 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9218
                 then ()
                 else
                   (let uu____9220 = lec_hd  in
                    match uu____9220 with
                    | (lb1,uu____9228,uu____9229) ->
                        let uu____9230 = lec2  in
                        (match uu____9230 with
                         | (lb2,uu____9238,uu____9239) ->
                             let msg =
                               let uu____9241 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9242 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9241 uu____9242
                                in
                             let uu____9243 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9243))
                  in
               let lecs1 =
                 let uu____9253 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9312 = univs_and_uvars_of_lec this_lec  in
                        match uu____9312 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9253 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9465 = lec_hd  in
                   match uu____9465 with
                   | (lbname,e,c) ->
                       let uu____9475 =
                         let uu____9480 =
                           let uu____9481 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____9482 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____9483 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9481 uu____9482 uu____9483
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9480)
                          in
                       let uu____9484 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9475 uu____9484
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9514  ->
                         match uu____9514 with
                         | (u,k) ->
                             let uu____9527 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____9527 with
                              | FStar_Pervasives_Native.Some uu____9536 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9543 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____9547 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____9547 with
                                   | (bs,kres) ->
                                       ((let uu____9585 =
                                           let uu____9586 =
                                             let uu____9589 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____9589
                                              in
                                           uu____9586.FStar_Syntax_Syntax.n
                                            in
                                         match uu____9585 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9590 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____9594 =
                                               let uu____9595 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____9595
                                                in
                                             if uu____9594
                                             then fail kres
                                             else ()
                                         | uu____9597 -> fail kres);
                                        (let a =
                                           let uu____9599 =
                                             let uu____9602 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9602
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9599 kres
                                            in
                                         let t =
                                           let uu____9606 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Util.abs bs
                                             uu____9606
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
                      (fun uu____9725  ->
                         match uu____9725 with
                         | (lbname,e,c) ->
                             let uu____9771 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9840 ->
                                   let uu____9855 = (e, c)  in
                                   (match uu____9855 with
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
                                                (fun uu____9892  ->
                                                   match uu____9892 with
                                                   | (x,uu____9900) ->
                                                       let uu____9905 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9905)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9915 =
                                                let uu____9916 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9916
                                                 in
                                              if uu____9915
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
                                          let uu____9924 =
                                            let uu____9925 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9925.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9924 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9948 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9948 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9963 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9965 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9965, gen_tvars))
                                in
                             (match uu____9771 with
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
        (let uu____10111 = Obj.magic ()  in ());
        (let uu____10113 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10113
         then
           let uu____10114 =
             let uu____10115 =
               FStar_List.map
                 (fun uu____10128  ->
                    match uu____10128 with
                    | (lb,uu____10136,uu____10137) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10115 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10114
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10158  ->
                match uu____10158 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10187 = gen env is_rec lecs  in
           match uu____10187 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10286  ->
                       match uu____10286 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10348 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10348
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10392  ->
                           match uu____10392 with
                           | (l,us,e,c,gvs) ->
                               let uu____10426 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____10427 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____10428 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____10429 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____10430 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10426 uu____10427 uu____10428
                                 uu____10429 uu____10430))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10471  ->
                match uu____10471 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10515 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____10515, t, c, gvs)) univnames_lecs
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
          let check env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____10558 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____10558 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10564 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10564)
             in
          let is_var e1 =
            let uu____10571 =
              let uu____10572 = FStar_Syntax_Subst.compress e1  in
              uu____10572.FStar_Syntax_Syntax.n  in
            match uu____10571 with
            | FStar_Syntax_Syntax.Tm_name uu____10575 -> true
            | uu____10576 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___123_10592 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___123_10592.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___123_10592.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10593 -> e2  in
          let env2 =
            let uu___124_10595 = env1  in
            let uu____10596 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___124_10595.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___124_10595.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___124_10595.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___124_10595.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___124_10595.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___124_10595.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___124_10595.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___124_10595.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___124_10595.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___124_10595.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___124_10595.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___124_10595.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___124_10595.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___124_10595.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___124_10595.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10596;
              FStar_TypeChecker_Env.is_iface =
                (uu___124_10595.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___124_10595.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___124_10595.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___124_10595.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___124_10595.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___124_10595.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___124_10595.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___124_10595.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___124_10595.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___124_10595.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___124_10595.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___124_10595.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___124_10595.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___124_10595.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___124_10595.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___124_10595.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___124_10595.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___124_10595.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___124_10595.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____10597 = check env2 t1 t2  in
          match uu____10597 with
          | FStar_Pervasives_Native.None  ->
              let uu____10604 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____10609 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____10604 uu____10609
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10616 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10616
                then
                  let uu____10617 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10617
                else ());
               (let uu____10619 = decorate e t2  in (uu____10619, g)))
  
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
        let uu____10647 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____10647
        then
          let uu____10652 = discharge g1  in
          let uu____10653 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____10652, uu____10653)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm]  in
           let c1 =
             let uu____10660 =
               let uu____10661 =
                 let uu____10662 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____10662 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____10661
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____10660
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____10664 = destruct_comp c1  in
           match uu____10664 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10681 = FStar_TypeChecker_Env.get_range env  in
                 let uu____10682 =
                   let uu____10683 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____10684 =
                     let uu____10685 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____10686 =
                       let uu____10689 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____10689]  in
                     uu____10685 :: uu____10686  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10683 uu____10684  in
                 uu____10682 FStar_Pervasives_Native.None uu____10681  in
               ((let uu____10693 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____10693
                 then
                   let uu____10694 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10694
                 else ());
                (let g2 =
                   let uu____10697 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10697  in
                 let uu____10698 = discharge g2  in
                 let uu____10699 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____10698, uu____10699))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___89_10723 =
        match uu___89_10723 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10731)::[] -> f fst1
        | uu____10748 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10753 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10753
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44)
         in
      let op_or_e e =
        let uu____10762 =
          let uu____10765 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10765  in
        FStar_All.pipe_right uu____10762
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46)
         in
      let op_or_t t =
        let uu____10776 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10776
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
         in
      let short_op_ite uu___90_10790 =
        match uu___90_10790 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10798)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10817)::[] ->
            let uu____10846 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10846
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10851 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10861 =
          let uu____10868 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10868)  in
        let uu____10873 =
          let uu____10882 =
            let uu____10889 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10889)  in
          let uu____10894 =
            let uu____10903 =
              let uu____10910 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10910)  in
            let uu____10915 =
              let uu____10924 =
                let uu____10931 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10931)  in
              let uu____10936 =
                let uu____10945 =
                  let uu____10952 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10952)  in
                [uu____10945; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10924 :: uu____10936  in
            uu____10903 :: uu____10915  in
          uu____10882 :: uu____10894  in
        uu____10861 :: uu____10873  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11003 =
            FStar_Util.find_map table
              (fun uu____11016  ->
                 match uu____11016 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11033 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11033
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11003 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11036 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11040 =
      let uu____11041 = FStar_Syntax_Util.un_uinst l  in
      uu____11041.FStar_Syntax_Syntax.n  in
    match uu____11040 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11045 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11069)::uu____11070 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11081 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11088,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11089))::uu____11090 -> bs
      | uu____11107 ->
          let uu____11108 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11108 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11112 =
                 let uu____11113 = FStar_Syntax_Subst.compress t  in
                 uu____11113.FStar_Syntax_Syntax.n  in
               (match uu____11112 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11117) ->
                    let uu____11134 =
                      FStar_Util.prefix_until
                        (fun uu___91_11174  ->
                           match uu___91_11174 with
                           | (uu____11181,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11182)) ->
                               false
                           | uu____11185 -> true) bs'
                       in
                    (match uu____11134 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11220,uu____11221) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11293,uu____11294) ->
                         let uu____11367 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11385  ->
                                   match uu____11385 with
                                   | (x,uu____11393) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____11367
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11440  ->
                                     match uu____11440 with
                                     | (x,i) ->
                                         let uu____11459 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11459, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11469 -> bs))
  
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
            if
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
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
          let uu____11501 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11501
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
        (let uu____11524 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11524
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11526 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11526))
         else ());
        (let fv =
           let uu____11529 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11529
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def;
                FStar_Syntax_Syntax.lbattrs = []
              }])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____11539 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___125_11545 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___125_11545.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___125_11545.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___125_11545.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___125_11545.FStar_Syntax_Syntax.sigattrs)
           }), uu____11539))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      let visibility uu___92_11555 =
        match uu___92_11555 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11556 -> false  in
      let reducibility uu___93_11560 =
        match uu___93_11560 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11561 -> false  in
      let assumption uu___94_11565 =
        match uu___94_11565 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11566 -> false  in
      let reification uu___95_11570 =
        match uu___95_11570 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11571 -> true
        | uu____11572 -> false  in
      let inferred uu___96_11576 =
        match uu___96_11576 with
        | FStar_Syntax_Syntax.Discriminator uu____11577 -> true
        | FStar_Syntax_Syntax.Projector uu____11578 -> true
        | FStar_Syntax_Syntax.RecordType uu____11583 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11592 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11601 -> false  in
      let has_eq uu___97_11605 =
        match uu___97_11605 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11606 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                         (inferred x))
                        || (visibility x))
                       || (assumption x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Inline_for_extraction))))
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
        | FStar_Syntax_Syntax.Reflectable uu____11666 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11671 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____11675 =
        let uu____11676 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___98_11680  ->
                  match uu___98_11680 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11681 -> false))
           in
        FStar_All.pipe_right uu____11676 Prims.op_Negation  in
      if uu____11675
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11694 =
            let uu____11699 =
              let uu____11700 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11700 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11699)  in
          FStar_Errors.raise_error uu____11694 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11708 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11712 =
            let uu____11713 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11713  in
          if uu____11712 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11718),uu____11719) ->
              ((let uu____11735 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11735
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11739 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11739
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11745 ->
              let uu____11754 =
                let uu____11755 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____11755  in
              if uu____11754 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11761 ->
              let uu____11768 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11768 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11772 ->
              let uu____11779 =
                let uu____11780 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11780  in
              if uu____11779 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11786 ->
              let uu____11787 =
                let uu____11788 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11788  in
              if uu____11787 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11794 ->
              let uu____11795 =
                let uu____11796 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11796  in
              if uu____11795 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11802 ->
              let uu____11815 =
                let uu____11816 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11816  in
              if uu____11815 then err'1 () else ()
          | uu____11822 -> ()))
      else ()
  
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____11885 =
                            let uu____11888 =
                              let uu____11889 =
                                let uu____11896 =
                                  let uu____11897 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11897
                                   in
                                (uu____11896, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____11889  in
                            FStar_Syntax_Syntax.mk uu____11888  in
                          uu____11885 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11938  ->
                                  match uu____11938 with
                                  | (x,imp) ->
                                      let uu____11949 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____11949, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____11951 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____11951  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11960 =
                               let uu____11961 =
                                 let uu____11962 =
                                   let uu____11963 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____11964 =
                                     let uu____11965 =
                                       let uu____11966 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11966
                                        in
                                     [uu____11965]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11963
                                     uu____11964
                                    in
                                 uu____11962 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____11961  in
                             FStar_Syntax_Util.refine x uu____11960  in
                           let uu____11969 =
                             let uu___126_11970 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___126_11970.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___126_11970.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____11969)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____11985 =
                          FStar_List.map
                            (fun uu____12007  ->
                               match uu____12007 with
                               | (x,uu____12019) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____11985 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12068  ->
                                match uu____12068 with
                                | (x,uu____12080) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             (let uu____12094 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12094)
                               ||
                               (let uu____12096 =
                                  let uu____12097 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____12097.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____12096)
                              in
                           let quals =
                             let uu____12101 =
                               FStar_List.filter
                                 (fun uu___99_12105  ->
                                    match uu___99_12105 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____12106 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____12101
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____12127 =
                                 let uu____12128 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12128  in
                               FStar_Syntax_Syntax.mk_Total uu____12127  in
                             let uu____12129 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12129
                              in
                           let decl =
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng =
                                 (FStar_Ident.range_of_lid discriminator_name);
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____12132 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____12132
                            then
                              let uu____12133 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12133
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Util.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____12186  ->
                                               match uu____12186 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12210 =
                                                       let uu____12213 =
                                                         let uu____12214 =
                                                           let uu____12221 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____12221,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12214
                                                          in
                                                       pos uu____12213  in
                                                     (uu____12210, b)
                                                   else
                                                     (let uu____12225 =
                                                        let uu____12228 =
                                                          let uu____12229 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12229
                                                           in
                                                        pos uu____12228  in
                                                      (uu____12225, b))))
                                      in
                                   let pat_true =
                                     let uu____12247 =
                                       let uu____12250 =
                                         let uu____12251 =
                                           let uu____12264 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____12264, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12251
                                          in
                                       pos uu____12250  in
                                     (uu____12247,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____12298 =
                                       let uu____12301 =
                                         let uu____12302 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12302
                                          in
                                       pos uu____12301  in
                                     (uu____12298,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____12314 =
                                     let uu____12317 =
                                       let uu____12318 =
                                         let uu____12341 =
                                           let uu____12344 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____12345 =
                                             let uu____12348 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____12348]  in
                                           uu____12344 :: uu____12345  in
                                         (arg_exp, uu____12341)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12318
                                        in
                                     FStar_Syntax_Syntax.mk uu____12317  in
                                   uu____12314 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____12355 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____12355
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____12363 =
                                  let uu____12368 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____12368  in
                                let uu____12369 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12363;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12369;
                                  FStar_Syntax_Syntax.lbattrs = []
                                }  in
                              let impl =
                                let uu____12375 =
                                  let uu____12376 =
                                    let uu____12383 =
                                      let uu____12386 =
                                        let uu____12387 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____12387
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____12386]  in
                                    ((false, [lb]), uu____12383)  in
                                  FStar_Syntax_Syntax.Sig_let uu____12376  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12375;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____12405 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____12405
                               then
                                 let uu____12406 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12406
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____12448  ->
                                  match uu____12448 with
                                  | (a,uu____12454) ->
                                      let uu____12455 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____12455 with
                                       | (field_name,uu____12461) ->
                                           let field_proj_tm =
                                             let uu____12463 =
                                               let uu____12464 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12464
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12463 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____12481 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12513  ->
                                    match uu____12513 with
                                    | (x,uu____12521) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____12523 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____12523 with
                                         | (field_name,uu____12531) ->
                                             let t =
                                               let uu____12533 =
                                                 let uu____12534 =
                                                   let uu____12537 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12537
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12534
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12533
                                                in
                                             let only_decl =
                                               (let uu____12541 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env
                                                   in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12541)
                                                 ||
                                                 (let uu____12543 =
                                                    let uu____12544 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____12544.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12543)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12558 =
                                                   FStar_List.filter
                                                     (fun uu___100_12562  ->
                                                        match uu___100_12562
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12563 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12558
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___101_12576  ->
                                                         match uu___101_12576
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12577 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
                                             let decl =
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   (FStar_Ident.range_of_lid
                                                      field_name);
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____12596 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____12596
                                               then
                                                 let uu____12597 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12597
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____12645 
                                                             ->
                                                             match uu____12645
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12669
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____12669,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12685
                                                                    =
                                                                    let uu____12688
                                                                    =
                                                                    let uu____12689
                                                                    =
                                                                    let uu____12696
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____12696,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12689
                                                                     in
                                                                    pos
                                                                    uu____12688
                                                                     in
                                                                    (uu____12685,
                                                                    b))
                                                                   else
                                                                    (let uu____12700
                                                                    =
                                                                    let uu____12703
                                                                    =
                                                                    let uu____12704
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12704
                                                                     in
                                                                    pos
                                                                    uu____12703
                                                                     in
                                                                    (uu____12700,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____12720 =
                                                     let uu____12723 =
                                                       let uu____12724 =
                                                         let uu____12737 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____12737,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12724
                                                        in
                                                     pos uu____12723  in
                                                   let uu____12746 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____12720,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12746)
                                                    in
                                                 let body =
                                                   let uu____12758 =
                                                     let uu____12761 =
                                                       let uu____12762 =
                                                         let uu____12785 =
                                                           let uu____12788 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____12788]  in
                                                         (arg_exp,
                                                           uu____12785)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12762
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12761
                                                      in
                                                   uu____12758
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____12796 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____12796
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____12803 =
                                                     let uu____12808 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____12808
                                                      in
                                                   let uu____12809 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12803;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12809;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = []
                                                   }  in
                                                 let impl =
                                                   let uu____12815 =
                                                     let uu____12816 =
                                                       let uu____12823 =
                                                         let uu____12826 =
                                                           let uu____12827 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____12827
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____12826]  in
                                                       ((false, [lb]),
                                                         uu____12823)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12816
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12815;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____12845 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____12845
                                                  then
                                                    let uu____12846 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12846
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____12481 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12886) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12891 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____12891 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____12913 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____12913 with
                    | (formals,uu____12929) ->
                        let uu____12946 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12978 =
                                   let uu____12979 =
                                     let uu____12980 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____12980  in
                                   FStar_Ident.lid_equals typ_lid uu____12979
                                    in
                                 if uu____12978
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12999,uvs',tps,typ0,uu____13003,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____13022 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____12946 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____13095 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____13095 with
                              | (indices,uu____13111) ->
                                  let refine_domain =
                                    let uu____13129 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___102_13134  ->
                                              match uu___102_13134 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13135 -> true
                                              | uu____13144 -> false))
                                       in
                                    if uu____13129
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___103_13152 =
                                      match uu___103_13152 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13155,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13167 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____13168 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____13168 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____13179 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____13179 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13244  ->
                                               fun uu____13245  ->
                                                 match (uu____13244,
                                                         uu____13245)
                                                 with
                                                 | ((x,uu____13263),(x',uu____13265))
                                                     ->
                                                     let uu____13274 =
                                                       let uu____13281 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____13281)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13274) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13282 -> []
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____13300 =
         let uu____13301 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____13301 haseq_suffix  in
       uu____13300 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)])
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple5)
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____13355 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____13369,bs,t,uu____13372,uu____13373) ->
                (lid, bs, t)
            | uu____13382 -> failwith "Impossible!"  in
          match uu____13355 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____13404 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____13404 t  in
              let uu____13411 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____13411 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____13435 =
                       let uu____13436 = FStar_Syntax_Subst.compress t2  in
                       uu____13436.FStar_Syntax_Syntax.n  in
                     match uu____13435 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____13446) -> ibs
                     | uu____13463 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____13470 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____13471 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____13470 uu____13471
                      in
                   let ind1 =
                     let uu____13477 =
                       let uu____13478 =
                         FStar_List.map
                           (fun uu____13491  ->
                              match uu____13491 with
                              | (bv,aq) ->
                                  let uu____13502 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____13502, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____13478  in
                     uu____13477 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____13508 =
                       let uu____13509 =
                         FStar_List.map
                           (fun uu____13522  ->
                              match uu____13522 with
                              | (bv,aq) ->
                                  let uu____13533 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____13533, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____13509  in
                     uu____13508 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____13539 =
                       let uu____13540 =
                         let uu____13541 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____13541]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____13540
                        in
                     uu____13539 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____13562 =
                            let uu____13563 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____13563  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____13562) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____13574 =
                              let uu____13575 =
                                let uu____13576 =
                                  let uu____13577 =
                                    let uu____13578 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____13578
                                     in
                                  [uu____13577]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____13576
                                 in
                              uu____13575 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____13574)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___127_13585 = fml  in
                     let uu____13586 =
                       let uu____13587 =
                         let uu____13594 =
                           let uu____13595 =
                             let uu____13606 =
                               let uu____13609 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____13609]  in
                             [uu____13606]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____13595  in
                         (fml, uu____13594)  in
                       FStar_Syntax_Syntax.Tm_meta uu____13587  in
                     {
                       FStar_Syntax_Syntax.n = uu____13586;
                       FStar_Syntax_Syntax.pos =
                         (uu___127_13585.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___127_13585.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____13622 =
                              let uu____13623 =
                                let uu____13624 =
                                  let uu____13625 =
                                    let uu____13626 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____13626
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____13625  in
                                [uu____13624]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____13623
                               in
                            uu____13622 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____13651 =
                              let uu____13652 =
                                let uu____13653 =
                                  let uu____13654 =
                                    let uu____13655 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____13655
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____13654  in
                                [uu____13653]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____13652
                               in
                            uu____13651 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  