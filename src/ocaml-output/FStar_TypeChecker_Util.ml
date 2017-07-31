open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____19 = FStar_TypeChecker_Env.get_range env in
      let uu____20 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____19 uu____20
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____25 =
      let uu____26 = FStar_Syntax_Subst.compress t in
      uu____26.FStar_Syntax_Syntax.n in
    match uu____25 with
    | FStar_Syntax_Syntax.Tm_type uu____29 -> true
    | uu____30 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____41 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____41
      (FStar_List.filter
         (fun uu____55  ->
            match uu____55 with
            | (x,uu____61) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____75 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____77 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____77) in
        if uu____75
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____79 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____79 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____88 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____88
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___102_98  ->
    match uu___102_98 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____100);
        FStar_Syntax_Syntax.pos = uu____101;
        FStar_Syntax_Syntax.vars = uu____102;_} -> uv
    | uu____129 -> failwith "Impossible"
let new_implicit_var:
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____158 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____158 with
          | FStar_Pervasives_Native.Some (uu____181::(tm,uu____183)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____235 ->
              let uu____246 = new_uvar_aux env k in
              (match uu____246 with
               | (t,u) ->
                   let g =
                     let uu___121_266 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____267 =
                       let uu____282 =
                         let uu____295 = as_uvar u in
                         (reason, env, uu____295, t, k, r) in
                       [uu____282] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___121_266.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___121_266.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___121_266.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____267
                     } in
                   let uu____320 =
                     let uu____327 =
                       let uu____332 = as_uvar u in (uu____332, r) in
                     [uu____327] in
                   (t, uu____320, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____362 =
        let uu____363 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____363 in
      if uu____362
      then
        let us =
          let uu____369 =
            let uu____372 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____390  ->
                 match uu____390 with
                 | (x,uu____396) -> FStar_Syntax_Print.uvar_to_string x)
              uu____372 in
          FStar_All.pipe_right uu____369 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____403 =
            let uu____404 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____404 in
          FStar_Errors.err r uu____403);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____419  ->
      match uu____419 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____429;
          FStar_Syntax_Syntax.lbdef = e;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname in
          let t1 = FStar_Syntax_Subst.compress t in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env in
                 let mk_binder1 scope a =
                   let uu____475 =
                     let uu____476 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____476.FStar_Syntax_Syntax.n in
                   match uu____475 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____483 = FStar_Syntax_Util.type_u () in
                       (match uu____483 with
                        | (k,uu____493) ->
                            let t2 =
                              let uu____495 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____495
                                FStar_Pervasives_Native.fst in
                            ((let uu___122_505 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___122_505.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___122_505.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____506 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____543) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____550) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____613) ->
                       let uu____634 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____694  ->
                                 fun uu____695  ->
                                   match (uu____694, uu____695) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____773 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____773 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____634 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____885 = aux must_check_ty1 scope body in
                            (match uu____885 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____914 =
                                         FStar_Options.ml_ish () in
                                       if uu____914
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____921 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____921
                                   then
                                     let uu____922 =
                                       FStar_Range.string_of_range r in
                                     let uu____923 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____924 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____922 uu____923 uu____924
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____934 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____948 =
                            let uu____953 =
                              let uu____954 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____954
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____953 in
                          (uu____948, false)) in
                 let uu____967 =
                   let uu____976 = t_binders env in aux false uu____976 e in
                 match uu____967 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1001 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____1001
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1005 =
                                let uu____1006 =
                                  let uu____1011 =
                                    let uu____1012 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____1012 in
                                  (uu____1011, rng) in
                                FStar_Errors.Error uu____1006 in
                              FStar_Exn.raise uu____1005)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1020 ->
               let uu____1021 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1021 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
let pat_as_exp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.pat)
          FStar_Pervasives_Native.tuple3
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
                  FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1123) ->
              let uu____1128 = FStar_Syntax_Util.type_u () in
              (match uu____1128 with
               | (k,uu____1152) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___123_1155 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_1155.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_1155.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____1156 =
                     let uu____1161 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____1161 t in
                   (match uu____1156 with
                    | (e,u) ->
                        let p2 =
                          let uu___124_1185 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___124_1185.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1195 = FStar_Syntax_Util.type_u () in
              (match uu____1195 with
               | (t,uu____1219) ->
                   let x1 =
                     let uu___125_1221 = x in
                     let uu____1222 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___125_1221.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___125_1221.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1222
                     } in
                   let env2 =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env1 x1
                     else env1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [], [x1], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1239 = FStar_Syntax_Util.type_u () in
              (match uu____1239 with
               | (t,uu____1263) ->
                   let x1 =
                     let uu___126_1265 = x in
                     let uu____1266 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___126_1265.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___126_1265.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1266
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1299 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1426  ->
                        fun uu____1427  ->
                          match (uu____1426, uu____1427) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1616 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1616 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____1299 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1814 =
                       let uu____1817 =
                         let uu____1818 =
                           let uu____1825 =
                             let uu____1828 =
                               let uu____1829 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1830 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1829
                                 uu____1830 in
                             uu____1828 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1825,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1818 in
                       FStar_Syntax_Syntax.mk uu____1817 in
                     uu____1814 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1842 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1853 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1864 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1842, uu____1853, uu____1864, env2, e,
                     (let uu___127_1886 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___127_1886.FStar_Syntax_Syntax.p)
                      }))) in
        let rec elaborate_pat env1 p1 =
          let maybe_dot inaccessible a r =
            if allow_implicits && inaccessible
            then
              FStar_Syntax_Syntax.withinfo
                (FStar_Syntax_Syntax.Pat_dot_term
                   (a, FStar_Syntax_Syntax.tun)) r
            else
              FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a) r in
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats1 =
                FStar_List.map
                  (fun uu____1970  ->
                     match uu____1970 with
                     | (p2,imp) ->
                         let uu____1989 = elaborate_pat env1 p2 in
                         (uu____1989, imp)) pats in
              let uu____1994 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1994 with
               | (uu____2001,t) ->
                   let uu____2003 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____2003 with
                    | (f,uu____2019) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____2141::uu____2142) ->
                              FStar_Exn.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____2193::uu____2194,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____2272  ->
                                      match uu____2272 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____2299 =
                                                   let uu____2302 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____2302 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____2299
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____2304 =
                                                 maybe_dot inaccessible a r in
                                               (uu____2304, true)
                                           | uu____2309 ->
                                               let uu____2312 =
                                                 let uu____2313 =
                                                   let uu____2318 =
                                                     let uu____2319 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2319 in
                                                   (uu____2318,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____2313 in
                                               FStar_Exn.raise uu____2312)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____2393,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____2394))
                                   when p_imp ->
                                   let uu____2397 = aux formals' pats' in
                                   (p2, true) :: uu____2397
                               | (uu____2414,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (FStar_Pervasives_Native.Some
                                          (p2.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun in
                                   let p3 =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                   let uu____2422 = aux formals' pats2 in
                                   (p3, true) :: uu____2422
                               | (uu____2439,imp) ->
                                   let uu____2445 =
                                     let uu____2452 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____2452) in
                                   let uu____2455 = aux formals' pats' in
                                   uu____2445 :: uu____2455) in
                        let uu___128_2470 = p1 in
                        let uu____2473 =
                          let uu____2474 =
                            let uu____2487 = aux f pats1 in (fv, uu____2487) in
                          FStar_Syntax_Syntax.Pat_cons uu____2474 in
                        {
                          FStar_Syntax_Syntax.v = uu____2473;
                          FStar_Syntax_Syntax.p =
                            (uu___128_2470.FStar_Syntax_Syntax.p)
                        }))
          | uu____2504 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____2538 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____2538 with
          | (b,a,w,env2,arg,p3) ->
              let uu____2591 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____2591 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____2615 =
                     let uu____2616 =
                       let uu____2621 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____2621, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____2616 in
                   FStar_Exn.raise uu____2615
               | uu____2638 -> (b, a, w, arg, p3)) in
        let uu____2647 = one_pat true env p in
        match uu____2647 with
        | (b,uu____2673,uu____2674,tm,p1) -> (b, tm, p1)
let decorate_pattern:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p in
          let e1 = FStar_Syntax_Util.unmeta e in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2722,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2724)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2729,FStar_Syntax_Syntax.Tm_constant uu____2730) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2734 =
                    let uu____2735 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2736 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2735 uu____2736 in
                  failwith uu____2734)
               else ();
               (let uu____2739 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2739
                then
                  let uu____2740 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2741 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2740
                    uu____2741
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___129_2745 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___129_2745.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___129_2745.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2749 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2749
                then
                  let uu____2750 =
                    let uu____2751 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2752 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2751 uu____2752 in
                  failwith uu____2750
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___130_2756 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___130_2756.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___130_2756.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2758),uu____2759) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2781 =
                  let uu____2782 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2782 in
                if uu____2781
                then
                  let uu____2783 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2783
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2802;
                FStar_Syntax_Syntax.vars = uu____2803;_},args))
              ->
              ((let uu____2842 =
                  let uu____2843 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2843 Prims.op_Negation in
                if uu____2842
                then
                  let uu____2844 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2844
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2980)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3055) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3092) ->
                           let pat =
                             let uu____3114 = aux argpat e2 in
                             let uu____3115 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3114, uu____3115) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3120 ->
                      let uu____3143 =
                        let uu____3144 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3145 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3144 uu____3145 in
                      failwith uu____3143 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3157;
                     FStar_Syntax_Syntax.vars = uu____3158;_},uu____3159);
                FStar_Syntax_Syntax.pos = uu____3160;
                FStar_Syntax_Syntax.vars = uu____3161;_},args))
              ->
              ((let uu____3204 =
                  let uu____3205 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3205 Prims.op_Negation in
                if uu____3204
                then
                  let uu____3206 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3206
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3342)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3417) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3454) ->
                           let pat =
                             let uu____3476 = aux argpat e2 in
                             let uu____3477 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3476, uu____3477) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3482 ->
                      let uu____3505 =
                        let uu____3506 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3507 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3506 uu____3507 in
                      failwith uu____3505 in
                match_args [] args argpats))
          | uu____3516 ->
              let uu____3521 =
                let uu____3522 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3523 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3524 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3522 uu____3523 uu____3524 in
              failwith uu____3521 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____3562 =
      match uu____3562 with
      | (p,i) ->
          let uu____3579 = decorated_pattern_as_term p in
          (match uu____3579 with
           | (vars,te) ->
               let uu____3602 =
                 let uu____3607 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3607) in
               (vars, uu____3602)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3621 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3621)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3625 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3625)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3629 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3629)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3650 =
          let uu____3665 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3665 FStar_List.unzip in
        (match uu____3650 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3775 =
               let uu____3776 =
                 let uu____3777 =
                   let uu____3792 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3792, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3777 in
               mk1 uu____3776 in
             (vars1, uu____3775))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3833)::[] -> wp
      | uu____3850 ->
          let uu____3859 =
            let uu____3860 =
              let uu____3861 =
                FStar_List.map
                  (fun uu____3871  ->
                     match uu____3871 with
                     | (x,uu____3877) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3861 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3860 in
          failwith uu____3859 in
    let uu____3882 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3882, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3899 = destruct_comp c in
        match uu____3899 with
        | (u,uu____3907,wp) ->
            let uu____3909 =
              let uu____3918 =
                let uu____3919 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____3919 in
              [uu____3918] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3909;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3932 =
          let uu____3939 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____3940 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____3939 uu____3940 in
        match uu____3932 with | (m,uu____3942,uu____3943) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3956 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____3956
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
let lift_and_destruct:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
        let uu____3996 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____3996 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4033 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4033 with
             | (a,kwp) ->
                 let uu____4064 = destruct_comp m1 in
                 let uu____4071 = destruct_comp m2 in
                 ((md, a, kwp), uu____4064, uu____4071))
let is_pure_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
let is_pure_or_ghost_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
let mk_comp_l:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____4142 =
              let uu____4143 =
                let uu____4152 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4152] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4143;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4142
let mk_comp:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname
let lax_mk_tot_or_comp_l:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          if FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let subst_lcomp:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst1  ->
    fun lc  ->
      let uu___131_4202 = lc in
      let uu____4203 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___131_4202.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4203;
        FStar_Syntax_Syntax.cflags =
          (uu___131_4202.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4208  ->
             let uu____4209 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4209)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4214 =
      let uu____4215 = FStar_Syntax_Subst.compress t in
      uu____4215.FStar_Syntax_Syntax.n in
    match uu____4214 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4218 -> true
    | uu____4231 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4248 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4248
        then c
        else
          (let uu____4250 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4250
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4289 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4289] in
                       let us =
                         let uu____4293 =
                           let uu____4296 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4296] in
                         u_res :: uu____4293 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4300 =
                         let uu____4301 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4302 =
                           let uu____4303 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4304 =
                             let uu____4307 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4308 =
                               let uu____4311 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4311] in
                             uu____4307 :: uu____4308 in
                           uu____4303 :: uu____4304 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4301 uu____4302 in
                       uu____4300 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4315 = destruct_comp c1 in
              match uu____4315 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name in
                  let wp1 = close_wp u_res_t md res_t bvs wp in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
let close_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let close1 uu____4346 =
          let uu____4347 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4347 in
        let uu___132_4348 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_4348.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_4348.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_4348.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = close1
        }
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v1  ->
        let c =
          let uu____4362 =
            let uu____4363 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4363 in
          if uu____4362
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4368 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4368
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4370 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4370 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____4378 =
                        let uu____4379 =
                          let uu____4380 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____4381 =
                            let uu____4382 = FStar_Syntax_Syntax.as_arg t in
                            let uu____4383 =
                              let uu____4386 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____4386] in
                            uu____4382 :: uu____4383 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4380 uu____4381 in
                        uu____4379 FStar_Pervasives_Native.None
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.NoFullNorm] env
                        uu____4378) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____4390 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4390
         then
           let uu____4391 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4392 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4393 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4391
             uu____4392 uu____4393
         else ());
        c
let bind:
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____4416  ->
            match uu____4416 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4429 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4429
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4432 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4434 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4435 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4432 uu____4434 bstr uu____4435
                  else ());
                 (let bind_it uu____4440 =
                    let uu____4441 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4441
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4451 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4451
                        then
                          let uu____4452 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4454 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4455 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4456 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4457 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4452 uu____4454 uu____4455 uu____4456
                            uu____4457
                        else ());
                       (let try_simplify uu____4472 =
                          let aux uu____4486 =
                            let uu____4487 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4487
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4516 ->
                                  let uu____4517 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4517
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4544 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4544
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4600 =
                                  let uu____4605 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4605, reason) in
                                FStar_Util.Inl uu____4600
                            | uu____4610 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4629 =
                              let uu____4630 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4630.FStar_Syntax_Syntax.n in
                            match uu____4629 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4634) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4640 -> c in
                          let uu____4641 =
                            let uu____4642 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4642 in
                          if uu____4641
                          then
                            let uu____4655 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4655
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4675 =
                                  let uu____4676 =
                                    let uu____4681 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4681) in
                                  FStar_Errors.Error uu____4676 in
                                FStar_Exn.raise uu____4675))
                          else
                            (let uu____4693 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4693
                             then subst_c2 "both total"
                             else
                               (let uu____4705 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4705
                                then
                                  let uu____4716 =
                                    let uu____4721 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4721, "both gtot") in
                                  FStar_Util.Inl uu____4716
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4747 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4749 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4749) in
                                       if uu____4747
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___133_4762 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___133_4762.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___133_4762.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4763 =
                                           let uu____4768 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4768, "c1 Tot") in
                                         FStar_Util.Inl uu____4763
                                       else aux ()
                                   | uu____4774 -> aux ()))) in
                        let uu____4783 = try_simplify () in
                        match uu____4783 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4807 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4807
                              then
                                let uu____4808 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4809 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4810 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4808 uu____4809 uu____4810
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4819 = lift_and_destruct env c1 c2 in
                            (match uu____4819 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4876 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4876]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4878 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4878] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.mk_residual_comp
                                           FStar_Parser_Const.effect_Tot_lid
                                           FStar_Pervasives_Native.None
                                           [FStar_Syntax_Syntax.TOTAL])) in
                                 let r11 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_range r1))
                                     FStar_Pervasives_Native.None r1 in
                                 let wp_args =
                                   let uu____4891 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4892 =
                                     let uu____4895 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4896 =
                                       let uu____4899 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4900 =
                                         let uu____4903 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4904 =
                                           let uu____4907 =
                                             let uu____4908 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4908 in
                                           [uu____4907] in
                                         uu____4903 :: uu____4904 in
                                       uu____4899 :: uu____4900 in
                                     uu____4895 :: uu____4896 in
                                   uu____4891 :: uu____4892 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4913 =
                                     let uu____4914 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4914
                                       wp_args in
                                   uu____4913 FStar_Pervasives_Native.None
                                     t2.FStar_Syntax_Syntax.pos in
                                 mk_comp md u_t2 t2 wp []))) in
                  {
                    FStar_Syntax_Syntax.eff_name = joined_eff;
                    FStar_Syntax_Syntax.res_typ =
                      (lc21.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = [];
                    FStar_Syntax_Syntax.comp = bind_it
                  }))
let label:
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
let label_opt:
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4961 =
                let uu____4962 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4962 in
              if uu____4961
              then f
              else (let uu____4964 = reason1 () in label uu____4964 r f)
let label_guard:
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___134_4978 = g in
            let uu____4979 =
              let uu____4980 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4980 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4979;
              FStar_TypeChecker_Env.deferred =
                (uu___134_4978.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_4978.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_4978.FStar_TypeChecker_Env.implicits)
            }
let weaken_guard:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2 in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____4992 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5014 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5018 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5018
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5025 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5025
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5030 = destruct_comp c1 in
                    match uu____5030 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5046 =
                            let uu____5047 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5048 =
                              let uu____5049 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5050 =
                                let uu____5053 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5054 =
                                  let uu____5057 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5057] in
                                uu____5053 :: uu____5054 in
                              uu____5049 :: uu____5050 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5047
                              uu____5048 in
                          uu____5046 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___135_5060 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___135_5060.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___135_5060.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___135_5060.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = weaken
        }
let strengthen_precondition:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2
  =
  fun reason  ->
    fun env  ->
      fun e  ->
        fun lc  ->
          fun g0  ->
            let uu____5098 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5098
            then (lc, g0)
            else
              ((let uu____5105 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5105
                then
                  let uu____5106 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5107 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5106 uu____5107
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___103_5117  ->
                          match uu___103_5117 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5120 -> [])) in
                let strengthen uu____5126 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5134 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5134 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5141 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5143 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5143) in
                           if uu____5141
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5150 =
                                 let uu____5151 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5151 in
                               FStar_Syntax_Util.comp_set_flags uu____5150
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5157 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5157
                           then
                             let uu____5158 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5159 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5158 uu____5159
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5162 = destruct_comp c2 in
                           match uu____5162 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5178 =
                                   let uu____5179 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5180 =
                                     let uu____5181 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5182 =
                                       let uu____5185 =
                                         let uu____5186 =
                                           let uu____5187 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5187 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5186 in
                                       let uu____5188 =
                                         let uu____5191 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5191] in
                                       uu____5185 :: uu____5188 in
                                     uu____5181 :: uu____5182 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5179
                                     uu____5180 in
                                 uu____5178 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5195 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5195
                                 then
                                   let uu____5196 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5196
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5199 =
                  let uu___136_5200 = lc in
                  let uu____5201 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5202 =
                    let uu____5205 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5207 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5207) in
                    if uu____5205 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5201;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___136_5200.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5202;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5199,
                  (let uu___137_5212 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___137_5212.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___137_5212.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___137_5212.FStar_TypeChecker_Env.implicits)
                   }))))
let add_equality_to_post_condition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun comp  ->
      fun res_t  ->
        let md_pure =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid in
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let y = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____5230 =
          let uu____5235 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5236 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5235, uu____5236) in
        match uu____5230 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5245 =
                let uu____5246 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5247 =
                  let uu____5248 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5249 =
                    let uu____5252 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5252] in
                  uu____5248 :: uu____5249 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5246 uu____5247 in
              uu____5245 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5258 =
                let uu____5259 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5260 =
                  let uu____5261 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5262 =
                    let uu____5265 =
                      let uu____5266 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5266 in
                    let uu____5267 =
                      let uu____5270 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5270] in
                    uu____5265 :: uu____5267 in
                  uu____5261 :: uu____5262 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5259 uu____5260 in
              uu____5258 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5276 =
                let uu____5277 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5278 =
                  let uu____5279 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5280 =
                    let uu____5283 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5284 =
                      let uu____5287 =
                        let uu____5288 =
                          let uu____5289 =
                            let uu____5290 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5290] in
                          FStar_Syntax_Util.abs uu____5289 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5288 in
                      [uu____5287] in
                    uu____5283 :: uu____5284 in
                  uu____5279 :: uu____5280 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5277 uu____5278 in
              uu____5276 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5297 = FStar_TypeChecker_Env.get_range env in
              bind uu____5297 env FStar_Pervasives_Native.None
                (FStar_Syntax_Util.lcomp_of_comp comp)
                ((FStar_Pervasives_Native.Some x),
                  (FStar_Syntax_Util.lcomp_of_comp lc2)) in
            lc.FStar_Syntax_Syntax.comp ()
let ite:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.formula ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun guard  ->
      fun lcomp_then  ->
        fun lcomp_else  ->
          let joined_eff = join_lcomp env lcomp_then lcomp_else in
          let comp uu____5320 =
            let uu____5321 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5321
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5324 =
                 let uu____5349 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5350 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5349 uu____5350 in
               match uu____5324 with
               | ((md,uu____5352,uu____5353),(u_res_t,res_t,wp_then),
                  (uu____5357,uu____5358,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5396 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5397 =
                       let uu____5398 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5399 =
                         let uu____5400 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5401 =
                           let uu____5404 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5405 =
                             let uu____5408 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5409 =
                               let uu____5412 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5412] in
                             uu____5408 :: uu____5409 in
                           uu____5404 :: uu____5405 in
                         uu____5400 :: uu____5401 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5398 uu____5399 in
                     uu____5397 FStar_Pervasives_Native.None uu____5396 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5418 =
                     let uu____5419 = FStar_Options.split_cases () in
                     uu____5419 > (Prims.parse_int "0") in
                   if uu____5418
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5425 =
                          let uu____5426 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5427 =
                            let uu____5428 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5429 =
                              let uu____5432 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5432] in
                            uu____5428 :: uu____5429 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5426 uu____5427 in
                        uu____5425 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5435 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5435;
            FStar_Syntax_Syntax.res_typ =
              (lcomp_then.FStar_Syntax_Syntax.res_typ);
            FStar_Syntax_Syntax.cflags = [];
            FStar_Syntax_Syntax.comp = comp
          }
let fvar_const:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____5444 =
        let uu____5445 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5445 in
      FStar_Syntax_Syntax.fvar uu____5444 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5480  ->
                 match uu____5480 with
                 | (uu____5485,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5490 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5492 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5492
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5512 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5513 =
                 let uu____5514 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5515 =
                   let uu____5516 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5517 =
                     let uu____5520 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5521 =
                       let uu____5524 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5525 =
                         let uu____5528 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5528] in
                       uu____5524 :: uu____5525 in
                     uu____5520 :: uu____5521 in
                   uu____5516 :: uu____5517 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5514 uu____5515 in
               uu____5513 FStar_Pervasives_Native.None uu____5512 in
             let default_case =
               let post_k =
                 let uu____5535 =
                   let uu____5542 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5542] in
                 let uu____5543 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5535 uu____5543 in
               let kwp =
                 let uu____5549 =
                   let uu____5556 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5556] in
                 let uu____5557 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5549 uu____5557 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5562 =
                   let uu____5563 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5563] in
                 let uu____5564 =
                   let uu____5565 =
                     let uu____5568 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5568 in
                   let uu____5569 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5565 uu____5569 in
                 FStar_Syntax_Util.abs uu____5562 uu____5564
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.mk_residual_comp
                         FStar_Parser_Const.effect_Tot_lid
                         FStar_Pervasives_Native.None
                         [FStar_Syntax_Syntax.TOTAL])) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Parser_Const.effect_PURE_lid in
               mk_comp md u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____5593  ->
                    fun celse  ->
                      match uu____5593 with
                      | (g,cthen) ->
                          let uu____5601 =
                            let uu____5626 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5626 celse in
                          (match uu____5601 with
                           | ((md,uu____5628,uu____5629),(uu____5630,uu____5631,wp_then),
                              (uu____5633,uu____5634,wp_else)) ->
                               let uu____5654 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5654 []))
                 lcases default_case in
             let uu____5655 =
               let uu____5656 = FStar_Options.split_cases () in
               uu____5656 > (Prims.parse_int "0") in
             if uu____5655
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5660 = destruct_comp comp1 in
                match uu____5660 with
                | (uu____5667,uu____5668,wp) ->
                    let wp1 =
                      let uu____5673 =
                        let uu____5674 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5675 =
                          let uu____5676 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5677 =
                            let uu____5680 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5680] in
                          uu____5676 :: uu____5677 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5674 uu____5675 in
                      uu____5673 FStar_Pervasives_Native.None
                        wp.FStar_Syntax_Syntax.pos in
                    mk_comp md u_res_t res_t wp1 [])) in
        {
          FStar_Syntax_Syntax.eff_name = eff;
          FStar_Syntax_Syntax.res_typ = res_t;
          FStar_Syntax_Syntax.cflags = [];
          FStar_Syntax_Syntax.comp = bind_cases
        }
let maybe_assume_result_eq_pure_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let flags =
          let uu____5698 =
            ((let uu____5701 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5701) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5703 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5703) in
          if uu____5698
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5712 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5716 =
            (let uu____5719 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____5719) || env.FStar_TypeChecker_Env.lax in
          if uu____5716
          then c
          else
            (let uu____5723 = FStar_Syntax_Util.is_partial_return c in
             if uu____5723
             then c
             else
               (let uu____5727 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5727
                then
                  let uu____5730 =
                    let uu____5731 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5731 in
                  (if uu____5730
                   then
                     let uu____5734 =
                       let uu____5735 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5736 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5735 uu____5736 in
                     failwith uu____5734
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5741 =
                        let uu____5742 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5742 in
                      if uu____5741
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___138_5747 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___138_5747.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___138_5747.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___138_5747.FStar_Syntax_Syntax.effect_args);
                            FStar_Syntax_Syntax.flags = flags
                          } in
                        FStar_Syntax_Syntax.mk_Comp retc2
                      else FStar_Syntax_Util.comp_set_flags retc flags))
                else
                  (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                   let t = c1.FStar_Syntax_Syntax.result_typ in
                   let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret1 =
                     let uu____5758 =
                       let uu____5761 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5761
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5758 in
                   let eq1 =
                     let uu____5765 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5765 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5767 =
                     let uu____5768 =
                       let uu____5773 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5773.FStar_Syntax_Syntax.comp in
                     uu____5768 () in
                   FStar_Syntax_Util.comp_set_flags uu____5767 flags))) in
        let uu___139_5776 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___139_5776.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___139_5776.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = refine1
        }
let check_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____5805 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5805 with
          | FStar_Pervasives_Native.None  ->
              let uu____5814 =
                let uu____5815 =
                  let uu____5820 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5821 = FStar_TypeChecker_Env.get_range env in
                  (uu____5820, uu____5821) in
                FStar_Errors.Error uu____5815 in
              FStar_Exn.raise uu____5814
          | FStar_Pervasives_Native.Some g -> (e, c', g)
let maybe_coerce_bool_to_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
            let uu____5858 =
              let uu____5859 = FStar_Syntax_Subst.compress t2 in
              uu____5859.FStar_Syntax_Syntax.n in
            match uu____5858 with
            | FStar_Syntax_Syntax.Tm_type uu____5862 -> true
            | uu____5863 -> false in
          let uu____5864 =
            let uu____5865 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____5865.FStar_Syntax_Syntax.n in
          match uu____5864 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5873 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5884 =
                  let uu____5885 =
                    let uu____5886 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5886 in
                  (FStar_Pervasives_Native.None, uu____5885) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5884 in
              let e1 =
                let uu____5896 =
                  let uu____5897 =
                    let uu____5898 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5898] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5897 in
                uu____5896 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5903 -> (e, lc)
let weaken_result_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____5936 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5936 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5959 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5981 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5981, false)
            else
              (let uu____5987 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5987, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____5998) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___140_6003 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___140_6003.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___140_6003.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___140_6003.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6008 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6008 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___141_6016 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___141_6016.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___141_6016.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___141_6016.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___142_6019 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___142_6019.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___142_6019.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___142_6019.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6025 =
                     let uu____6026 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6026
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6031 =
                          let uu____6032 = FStar_Syntax_Subst.compress f1 in
                          uu____6032.FStar_Syntax_Syntax.n in
                        match uu____6031 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6037,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6039;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6040;_},uu____6041)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___143_6063 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___143_6063.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___143_6063.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___143_6063.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6064 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6069 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6069
                              then
                                let uu____6070 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6071 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6072 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6073 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6070 uu____6071 uu____6072 uu____6073
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6076 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6076 with
                              | (a,kwp) ->
                                  let k =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (a, t)] kwp in
                                  let md =
                                    FStar_TypeChecker_Env.get_effect_decl env
                                      ct.FStar_Syntax_Syntax.effect_name in
                                  let x =
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (t.FStar_Syntax_Syntax.pos)) t in
                                  let xexp = FStar_Syntax_Syntax.bv_to_name x in
                                  let uu____6089 = destruct_comp ct in
                                  (match uu____6089 with
                                   | (u_t,uu____6099,uu____6100) ->
                                       let wp =
                                         let uu____6104 =
                                           let uu____6105 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6106 =
                                             let uu____6107 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6108 =
                                               let uu____6111 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6111] in
                                             uu____6107 :: uu____6108 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6105 uu____6106 in
                                         uu____6104
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6115 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6115 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6125 =
                                             let uu____6126 =
                                               let uu____6127 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6127] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6126 in
                                           uu____6125
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6131 =
                                         let uu____6136 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6149 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6150 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6136
                                           uu____6149 e cret uu____6150 in
                                       (match uu____6131 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___144_6156 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___144_6156.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___144_6156.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6158 =
                                                let uu____6159 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6159 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6158
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6170 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6170
                                              then
                                                let uu____6171 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6171
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___104_6181  ->
                             match uu___104_6181 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6184 -> [])) in
                   let lc1 =
                     let uu___145_6186 = lc in
                     let uu____6187 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6187;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___146_6189 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___146_6189.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___146_6189.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___146_6189.FStar_TypeChecker_Env.implicits)
                     } in
                   (e, lc1, g2))
let pure_or_ghost_pre_and_post:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____6214 =
          let uu____6215 =
            let uu____6216 =
              let uu____6217 =
                let uu____6218 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6218 in
              [uu____6217] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6216 in
          uu____6215 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6214 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6225 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6225
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6243 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6258 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6287)::(ens,uu____6289)::uu____6290 ->
                    let uu____6319 =
                      let uu____6322 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6322 in
                    let uu____6323 =
                      let uu____6324 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6324 in
                    (uu____6319, uu____6323)
                | uu____6327 ->
                    let uu____6336 =
                      let uu____6337 =
                        let uu____6342 =
                          let uu____6343 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6343 in
                        (uu____6342, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6337 in
                    FStar_Exn.raise uu____6336)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6359)::uu____6360 ->
                    let uu____6379 =
                      let uu____6384 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6384 in
                    (match uu____6379 with
                     | (us_r,uu____6416) ->
                         let uu____6417 =
                           let uu____6422 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6422 in
                         (match uu____6417 with
                          | (us_e,uu____6454) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6457 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6457
                                  us_r in
                              let as_ens =
                                let uu____6459 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6459
                                  us_e in
                              let req =
                                let uu____6463 =
                                  let uu____6464 =
                                    let uu____6465 =
                                      let uu____6476 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6476] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6465 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6464 in
                                uu____6463 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6494 =
                                  let uu____6495 =
                                    let uu____6496 =
                                      let uu____6507 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6507] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6496 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6495 in
                                uu____6494 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6522 =
                                let uu____6525 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6525 in
                              let uu____6526 =
                                let uu____6527 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6527 in
                              (uu____6522, uu____6526)))
                | uu____6530 -> failwith "Impossible"))
let reify_body:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
      (let uu____6558 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6558
       then
         let uu____6559 = FStar_Syntax_Print.term_to_string tm in
         let uu____6560 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6559 uu____6560
       else ());
      tm'
let reify_body_with_arg:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
        (let uu____6581 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6581
         then
           let uu____6582 = FStar_Syntax_Print.term_to_string tm in
           let uu____6583 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6582
             uu____6583
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6589 =
      let uu____6590 =
        let uu____6591 = FStar_Syntax_Subst.compress t in
        uu____6591.FStar_Syntax_Syntax.n in
      match uu____6590 with
      | FStar_Syntax_Syntax.Tm_app uu____6594 -> false
      | uu____6609 -> true in
    if uu____6589
    then t
    else
      (let uu____6611 = FStar_Syntax_Util.head_and_args t in
       match uu____6611 with
       | (head1,args) ->
           let uu____6648 =
             let uu____6649 =
               let uu____6650 = FStar_Syntax_Subst.compress head1 in
               uu____6650.FStar_Syntax_Syntax.n in
             match uu____6649 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6653 -> false in
           if uu____6648
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6675 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
let maybe_instantiate:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____6715 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6715 with
             | (formals,uu____6729) ->
                 let n_implicits =
                   let uu____6747 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6823  ->
                             match uu____6823 with
                             | (uu____6830,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6747 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6961 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6961 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____6985 =
                     let uu____6986 =
                       let uu____6991 =
                         let uu____6992 = FStar_Util.string_of_int n_expected in
                         let uu____6999 = FStar_Syntax_Print.term_to_string e in
                         let uu____7000 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____6992 uu____6999 uu____7000 in
                       let uu____7007 = FStar_TypeChecker_Env.get_range env in
                       (uu____6991, uu____7007) in
                     FStar_Errors.Error uu____6986 in
                   FStar_Exn.raise uu____6985
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___105_7028 =
             match uu___105_7028 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7058 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7058 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____7167) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7210,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7243 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7243 with
                           | (v1,uu____7283,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7300 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7300 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7393 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7393)))
                      | (uu____7420,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7466 =
                      let uu____7493 = inst_n_binders t in
                      aux [] uu____7493 bs1 in
                    (match uu____7466 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7564) -> (e, torig, guard)
                          | (uu____7595,[]) when
                              let uu____7626 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7626 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7627 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7659 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7674 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7683 =
      let uu____7686 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7686
        (FStar_List.map
           (fun u  ->
              let uu____7696 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7696 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7683 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7715 = FStar_Util.set_is_empty x in
      if uu____7715
      then []
      else
        (let s =
           let uu____7722 =
             let uu____7725 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7725 in
           FStar_All.pipe_right uu____7722 FStar_Util.set_elements in
         (let uu____7733 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7733
          then
            let uu____7734 =
              let uu____7735 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7735 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7734
          else ());
         (let r =
            let uu____7742 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7742 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7757 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7757
                     then
                       let uu____7758 =
                         let uu____7759 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7759 in
                       let uu____7760 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7761 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7758 uu____7760 uu____7761
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name)) in
          u_names))
let gather_free_univnames:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env in
      let tm_univnames = FStar_Syntax_Free.univnames t in
      let univnames1 =
        let uu____7785 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7785 FStar_Util.fifo_set_elements in
      univnames1
let check_universe_generalization:
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____7822) -> generalized_univ_names
        | (uu____7829,[]) -> explicit_univ_names
        | uu____7836 ->
            let uu____7845 =
              let uu____7846 =
                let uu____7851 =
                  let uu____7852 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7852 in
                (uu____7851, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7846 in
            FStar_Exn.raise uu____7845
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0 in
      let univnames1 = gather_free_univnames env t in
      let univs1 = FStar_Syntax_Free.univs t in
      (let uu____7871 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7871
       then
         let uu____7872 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7872
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7878 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7878
        then
          let uu____7879 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7879
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in (univs2, ts)))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple3 Prims.list
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ecs  ->
      let uu____7932 =
        let uu____7933 =
          FStar_Util.for_all
            (fun uu____7943  ->
               match uu____7943 with
               | (uu____7950,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____7933 in
      if uu____7932
      then FStar_Pervasives_Native.None
      else
        (let norm1 c =
           (let uu____7984 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____7984
            then
              let uu____7985 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____7985
            else ());
           (let c1 =
              let uu____7988 = FStar_TypeChecker_Env.should_verify env in
              if uu____7988
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____7991 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____7991
             then
               let uu____7992 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7992
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____8053 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____8053 FStar_Util.set_elements in
         let uu____8140 =
           let uu____8175 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____8294  ->
                     match uu____8294 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm1 c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____8355 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____8355
                           then
                             let uu____8356 =
                               let uu____8357 =
                                 let uu____8360 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____8360
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____8357
                                 (FStar_String.concat ", ") in
                             let uu____8387 =
                               let uu____8388 =
                                 let uu____8391 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____8391
                                   (FStar_List.map
                                      (fun uu____8419  ->
                                         match uu____8419 with
                                         | (u,t2) ->
                                             let uu____8426 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____8427 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____8426 uu____8427)) in
                               FStar_All.pipe_right uu____8388
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____8356 uu____8387
                           else ());
                          (let univs2 =
                             let uu____8434 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____8457  ->
                                    match uu____8457 with
                                    | (uu____8466,t2) ->
                                        let uu____8468 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____8468) univs1 uu____8434 in
                           let uvs = gen_uvars uvt in
                           (let uu____8491 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____8491
                            then
                              let uu____8492 =
                                let uu____8493 =
                                  let uu____8496 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____8496
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____8493
                                  (FStar_String.concat ", ") in
                              let uu____8523 =
                                let uu____8524 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____8556  ->
                                          match uu____8556 with
                                          | (u,t2) ->
                                              let uu____8563 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____8564 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____8563 uu____8564)) in
                                FStar_All.pipe_right uu____8524
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____8492 uu____8523
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____8175 FStar_List.unzip in
         match uu____8140 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____8781 = FStar_List.hd univs1 in
               let uu____8786 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____8806 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____8806
                      then out
                      else
                        (let uu____8810 =
                           let uu____8811 =
                             let uu____8816 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____8816) in
                           FStar_Errors.Error uu____8811 in
                         FStar_Exn.raise uu____8810)) uu____8781 uu____8786 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____8823 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8823
               then
                 FStar_All.pipe_right gen_univs1
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.print1 "Generalizing uvar %s\n"
                           x.FStar_Ident.idText))
               else ());
              (let ecs1 =
                 FStar_All.pipe_right uvars1
                   (FStar_List.map
                      (fun uu____8904  ->
                         match uu____8904 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____8980  ->
                                       match uu____8980 with
                                       | (u,k) ->
                                           let uu____8993 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____8993 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9003;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9004;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____9011,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9013;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9014;_},uu____9015);
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9016;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9017;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____9044 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____9051 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____9055 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____9055 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____9093 =
                                                         let uu____9096 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____9096 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____9093 kres in
                                                     let t =
                                                       let uu____9100 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____9100
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____9104 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____9139 ->
                                   let uu____9154 = (e, c) in
                                   (match uu____9154 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e in
                                        let t =
                                          let uu____9170 =
                                            let uu____9171 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9171.FStar_Syntax_Syntax.n in
                                          match uu____9170 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9194 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9194 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____9209 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9211 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9211)) in
                             (match uu____9104 with
                              | (e1,c1) -> (gen_univs1, e1, c1)))) in
               FStar_Pervasives_Native.Some ecs1)))
let generalize:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____9279 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____9279
       then
         let uu____9280 =
           let uu____9281 =
             FStar_List.map
               (fun uu____9294  ->
                  match uu____9294 with
                  | (lb,uu____9302,uu____9303) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____9281 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____9280
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____9324  ->
              match uu____9324 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____9349 =
           let uu____9362 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____9397  ->
                     match uu____9397 with | (uu____9408,e,c) -> (e, c))) in
           gen env uu____9362 in
         match uu____9349 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____9473  ->
                     match uu____9473 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____9557  ->
                  fun uu____9558  ->
                    match (uu____9557, uu____9558) with
                    | ((l,uu____9610,uu____9611),(us,e,c)) ->
                        ((let uu____9646 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____9646
                          then
                            let uu____9647 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____9648 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____9649 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____9650 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____9647 uu____9648 uu____9649 uu____9650
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____9688  ->
              match uu____9688 with
              | (l,generalized_univs,t,c) ->
                  let uu____9719 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____9719, t, c)) univnames_lecs generalized_lecs)
let check_and_ascribe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
          let check env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____9764 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____9764 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9770 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____9770) in
          let is_var e1 =
            let uu____9777 =
              let uu____9778 = FStar_Syntax_Subst.compress e1 in
              uu____9778.FStar_Syntax_Syntax.n in
            match uu____9777 with
            | FStar_Syntax_Syntax.Tm_name uu____9781 -> true
            | uu____9782 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___147_9798 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___147_9798.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___147_9798.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9799 -> e2 in
          let env2 =
            let uu___148_9801 = env1 in
            let uu____9802 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_9801.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_9801.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_9801.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_9801.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_9801.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_9801.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_9801.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_9801.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_9801.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_9801.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_9801.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_9801.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_9801.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_9801.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_9801.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9802;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_9801.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_9801.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_9801.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_9801.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_9801.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_9801.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_9801.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_9801.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___148_9801.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___148_9801.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___148_9801.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___148_9801.FStar_TypeChecker_Env.identifier_info)
            } in
          let uu____9803 = check env2 t1 t2 in
          match uu____9803 with
          | FStar_Pervasives_Native.None  ->
              let uu____9810 =
                let uu____9811 =
                  let uu____9816 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____9817 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____9816, uu____9817) in
                FStar_Errors.Error uu____9811 in
              FStar_Exn.raise uu____9810
          | FStar_Pervasives_Native.Some g ->
              ((let uu____9824 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____9824
                then
                  let uu____9825 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____9825
                else ());
               (let uu____9827 = decorate e t2 in (uu____9827, g)))
let check_top_level:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
        let uu____9858 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____9858
        then
          let uu____9863 = discharge g1 in
          let uu____9864 = lc.FStar_Syntax_Syntax.comp () in
          (uu____9863, uu____9864)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____9877 =
               let uu____9878 =
                 let uu____9879 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____9879 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____9878
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____9877
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____9881 = destruct_comp c1 in
           match uu____9881 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____9898 = FStar_TypeChecker_Env.get_range env in
                 let uu____9899 =
                   let uu____9900 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____9901 =
                     let uu____9902 = FStar_Syntax_Syntax.as_arg t in
                     let uu____9903 =
                       let uu____9906 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____9906] in
                     uu____9902 :: uu____9903 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____9900 uu____9901 in
                 uu____9899 FStar_Pervasives_Native.None uu____9898 in
               ((let uu____9910 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____9910
                 then
                   let uu____9911 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____9911
                 else ());
                (let g2 =
                   let uu____9914 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____9914 in
                 let uu____9915 = discharge g2 in
                 let uu____9916 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____9915, uu____9916))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___106_9942 =
        match uu___106_9942 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____9950)::[] -> f fst1
        | uu____9967 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____9972 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____9972
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____9981 =
          let uu____9984 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____9984 in
        FStar_All.pipe_right uu____9981
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____9995 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____9995
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___107_10009 =
        match uu___107_10009 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10017)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10036)::[] ->
            let uu____10065 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10065
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____10070 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10080 =
          let uu____10087 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10087) in
        let uu____10092 =
          let uu____10101 =
            let uu____10108 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10108) in
          let uu____10113 =
            let uu____10122 =
              let uu____10129 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10129) in
            let uu____10134 =
              let uu____10143 =
                let uu____10150 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10150) in
              let uu____10155 =
                let uu____10164 =
                  let uu____10171 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10171) in
                [uu____10164; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10143 :: uu____10155 in
            uu____10122 :: uu____10134 in
          uu____10101 :: uu____10113 in
        uu____10080 :: uu____10092 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10222 =
            FStar_Util.find_map table
              (fun uu____10235  ->
                 match uu____10235 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10252 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10252
                     else FStar_Pervasives_Native.None) in
          (match uu____10222 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10255 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10260 =
      let uu____10261 = FStar_Syntax_Util.un_uinst l in
      uu____10261.FStar_Syntax_Syntax.n in
    match uu____10260 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10265 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10291)::uu____10292 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10303 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10310,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10311))::uu____10312 -> bs
      | uu____10329 ->
          let uu____10330 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10330 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10334 =
                 let uu____10335 = FStar_Syntax_Subst.compress t in
                 uu____10335.FStar_Syntax_Syntax.n in
               (match uu____10334 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10339) ->
                    let uu____10356 =
                      FStar_Util.prefix_until
                        (fun uu___108_10396  ->
                           match uu___108_10396 with
                           | (uu____10403,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10404)) ->
                               false
                           | uu____10407 -> true) bs' in
                    (match uu____10356 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10442,uu____10443) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10515,uu____10516) ->
                         let uu____10589 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10607  ->
                                   match uu____10607 with
                                   | (x,uu____10615) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10589
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10662  ->
                                     match uu____10662 with
                                     | (x,i) ->
                                         let uu____10681 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10681, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10691 -> bs))
let maybe_lift:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1 in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2 in
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
let maybe_monadic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c in
          let uu____10732 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____10732
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____10759 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____10759
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____10761 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____10761))
         else ());
        (let fv =
           let uu____10764 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10764
             FStar_Pervasives_Native.None in
         let lbname = FStar_Util.Inr fv in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def
              }]) in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident])) in
         let uu____10772 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___149_10778 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_10778.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_10778.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_10778.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___149_10778.FStar_Syntax_Syntax.sigattrs)
           }), uu____10772))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___109_10790 =
        match uu___109_10790 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10791 -> false in
      let reducibility uu___110_10795 =
        match uu___110_10795 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10796 -> false in
      let assumption uu___111_10800 =
        match uu___111_10800 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10801 -> false in
      let reification uu___112_10805 =
        match uu___112_10805 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10806 -> true
        | uu____10807 -> false in
      let inferred uu___113_10811 =
        match uu___113_10811 with
        | FStar_Syntax_Syntax.Discriminator uu____10812 -> true
        | FStar_Syntax_Syntax.Projector uu____10813 -> true
        | FStar_Syntax_Syntax.RecordType uu____10818 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____10827 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____10836 -> false in
      let has_eq uu___114_10840 =
        match uu___114_10840 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____10841 -> false in
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
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (visibility x))
                         || (reducibility x))
                        || (reification x))
                       || (inferred x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Assumption))))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
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
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Reflectable uu____10901 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10906 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____10910 =
        let uu____10911 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___115_10915  ->
                  match uu___115_10915 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10916 -> false)) in
        FStar_All.pipe_right uu____10911 Prims.op_Negation in
      if uu____10910
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____10929 =
            let uu____10930 =
              let uu____10935 =
                let uu____10936 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____10936 msg in
              (uu____10935, r) in
            FStar_Errors.Error uu____10930 in
          FStar_Exn.raise uu____10929 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____10944 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____10948 =
            let uu____10949 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____10949 in
          if uu____10948 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____10954),uu____10955) ->
              ((let uu____10971 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____10971
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____10975 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____10975
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____10981 ->
              let uu____10990 =
                let uu____10991 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____10991 in
              if uu____10990 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____10997 ->
              let uu____11004 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11004 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11008 ->
              let uu____11015 =
                let uu____11016 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11016 in
              if uu____11015 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11022 ->
              let uu____11023 =
                let uu____11024 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11024 in
              if uu____11023 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11030 ->
              let uu____11031 =
                let uu____11032 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11032 in
              if uu____11031 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11038 ->
              let uu____11051 =
                let uu____11052 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11052 in
              if uu____11051 then err'1 () else ()
          | uu____11058 -> ()))
      else ()
let mk_discriminator_and_indexed_projectors:
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
                      FStar_Syntax_Syntax.sigelt Prims.list
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
                      let p = FStar_Ident.range_of_lid lid in
                      let pos q = FStar_Syntax_Syntax.withinfo q p in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          let uu____11131 =
                            let uu____11134 =
                              let uu____11135 =
                                let uu____11142 =
                                  let uu____11143 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11143 in
                                (uu____11142, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11135 in
                            FStar_Syntax_Syntax.mk uu____11134 in
                          uu____11131 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11184  ->
                                  match uu____11184 with
                                  | (x,imp) ->
                                      let uu____11195 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11195, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11197 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11197 in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None in
                             let uu____11206 =
                               let uu____11207 =
                                 let uu____11208 =
                                   let uu____11209 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11210 =
                                     let uu____11211 =
                                       let uu____11212 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11212 in
                                     [uu____11211] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11209
                                     uu____11210 in
                                 uu____11208 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11207 in
                             FStar_Syntax_Util.refine x uu____11206 in
                           let uu____11215 =
                             let uu___150_11216 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_11216.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_11216.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11215) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11231 =
                          FStar_List.map
                            (fun uu____11253  ->
                               match uu____11253 with
                               | (x,uu____11265) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11231 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11314  ->
                                match uu____11314 with
                                | (x,uu____11326) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____11340 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11340)
                               ||
                               (let uu____11342 =
                                  let uu____11343 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11343.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11342) in
                           let quals =
                             let uu____11347 =
                               let uu____11350 =
                                 let uu____11353 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11353
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11357 =
                                 FStar_List.filter
                                   (fun uu___116_11361  ->
                                      match uu___116_11361 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11362 -> false) iquals in
                               FStar_List.append uu____11350 uu____11357 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11347 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11383 =
                                 let uu____11384 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11384 in
                               FStar_Syntax_Syntax.mk_Total uu____11383 in
                             let uu____11385 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11385 in
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
                             } in
                           (let uu____11388 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11388
                            then
                              let uu____11389 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11389
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
                                             fun uu____11442  ->
                                               match uu____11442 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11466 =
                                                       let uu____11469 =
                                                         let uu____11470 =
                                                           let uu____11477 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11477,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11470 in
                                                       pos uu____11469 in
                                                     (uu____11466, b)
                                                   else
                                                     (let uu____11481 =
                                                        let uu____11484 =
                                                          let uu____11485 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11485 in
                                                        pos uu____11484 in
                                                      (uu____11481, b)))) in
                                   let pat_true =
                                     let uu____11503 =
                                       let uu____11506 =
                                         let uu____11507 =
                                           let uu____11520 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11520, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11507 in
                                       pos uu____11506 in
                                     (uu____11503,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____11554 =
                                       let uu____11557 =
                                         let uu____11558 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____11558 in
                                       pos uu____11557 in
                                     (uu____11554,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____11570 =
                                     let uu____11573 =
                                       let uu____11574 =
                                         let uu____11597 =
                                           let uu____11600 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____11601 =
                                             let uu____11604 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____11604] in
                                           uu____11600 :: uu____11601 in
                                         (arg_exp, uu____11597) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11574 in
                                     FStar_Syntax_Syntax.mk uu____11573 in
                                   uu____11570 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____11611 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____11611
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun in
                              let lb =
                                let uu____11619 =
                                  let uu____11624 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____11624 in
                                let uu____11625 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____11619;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____11625
                                } in
                              let impl =
                                let uu____11629 =
                                  let uu____11630 =
                                    let uu____11637 =
                                      let uu____11640 =
                                        let uu____11641 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____11641
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____11640] in
                                    ((false, [lb]), uu____11637) in
                                  FStar_Syntax_Syntax.Sig_let uu____11630 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____11629;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____11659 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____11659
                               then
                                 let uu____11660 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____11660
                               else ());
                              [decl; impl])) in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder) in
                      let binders =
                        FStar_List.append imp_binders [arg_binder] in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____11702  ->
                                  match uu____11702 with
                                  | (a,uu____11708) ->
                                      let uu____11709 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____11709 with
                                       | (field_name,uu____11715) ->
                                           let field_proj_tm =
                                             let uu____11717 =
                                               let uu____11718 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____11718 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____11717 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____11735 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____11766  ->
                                    match uu____11766 with
                                    | (x,uu____11774) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____11776 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____11776 with
                                         | (field_name,uu____11784) ->
                                             let t =
                                               let uu____11786 =
                                                 let uu____11787 =
                                                   let uu____11790 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____11790 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____11787 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____11786 in
                                             let only_decl =
                                               (let uu____11794 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____11794)
                                                 ||
                                                 (let uu____11796 =
                                                    let uu____11797 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____11797.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____11796) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____11811 =
                                                   FStar_List.filter
                                                     (fun uu___117_11815  ->
                                                        match uu___117_11815
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____11816 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____11811
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___118_11829  ->
                                                         match uu___118_11829
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____11830 ->
                                                             false)) in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1) in
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
                                                   = []
                                               } in
                                             ((let uu____11833 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____11833
                                               then
                                                 let uu____11834 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____11834
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____11882 
                                                             ->
                                                             match uu____11882
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____11906
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____11906,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____11922
                                                                    =
                                                                    let uu____11925
                                                                    =
                                                                    let uu____11926
                                                                    =
                                                                    let uu____11933
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____11933,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____11926 in
                                                                    pos
                                                                    uu____11925 in
                                                                    (uu____11922,
                                                                    b))
                                                                   else
                                                                    (let uu____11937
                                                                    =
                                                                    let uu____11940
                                                                    =
                                                                    let uu____11941
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____11941 in
                                                                    pos
                                                                    uu____11940 in
                                                                    (uu____11937,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____11957 =
                                                     let uu____11960 =
                                                       let uu____11961 =
                                                         let uu____11974 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____11974,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____11961 in
                                                     pos uu____11960 in
                                                   let uu____11983 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____11957,
                                                     FStar_Pervasives_Native.None,
                                                     uu____11983) in
                                                 let body =
                                                   let uu____11995 =
                                                     let uu____11998 =
                                                       let uu____11999 =
                                                         let uu____12022 =
                                                           let uu____12025 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12025] in
                                                         (arg_exp,
                                                           uu____12022) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____11999 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____11998 in
                                                   uu____11995
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12033 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12033
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun in
                                                 let lb =
                                                   let uu____12040 =
                                                     let uu____12045 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12045 in
                                                   let uu____12046 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12040;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12046
                                                   } in
                                                 let impl =
                                                   let uu____12050 =
                                                     let uu____12051 =
                                                       let uu____12058 =
                                                         let uu____12061 =
                                                           let uu____12062 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12062
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12061] in
                                                       ((false, [lb]),
                                                         uu____12058) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12051 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12050;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = []
                                                   } in
                                                 (let uu____12080 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12080
                                                  then
                                                    let uu____12081 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12081
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____11735 FStar_List.flatten in
                      FStar_List.append discriminator_ses projectors_ses
let mk_data_operations:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12125) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12130 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12130 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12152 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12152 with
                    | (formals,uu____12168) ->
                        let uu____12185 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12217 =
                                   let uu____12218 =
                                     let uu____12219 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12219 in
                                   FStar_Ident.lid_equals typ_lid uu____12218 in
                                 if uu____12217
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12238,uvs',tps,typ0,uu____12242,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12261 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____12185 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12334 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12334 with
                              | (indices,uu____12350) ->
                                  let refine_domain =
                                    let uu____12368 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___119_12373  ->
                                              match uu___119_12373 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12374 -> true
                                              | uu____12383 -> false)) in
                                    if uu____12368
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___120_12391 =
                                      match uu___120_12391 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12394,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12406 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12407 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12407 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals in
                                  let fields =
                                    let uu____12418 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12418 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12483  ->
                                               fun uu____12484  ->
                                                 match (uu____12483,
                                                         uu____12484)
                                                 with
                                                 | ((x,uu____12502),(x',uu____12504))
                                                     ->
                                                     let uu____12513 =
                                                       let uu____12520 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12520) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12513) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12521 -> []