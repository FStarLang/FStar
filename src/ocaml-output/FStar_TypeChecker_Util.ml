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
    | FStar_Syntax_Syntax.Tm_type uu____31 -> true
    | uu____32 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____43 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____43
      (FStar_List.filter
         (fun uu____57  ->
            match uu____57 with
            | (x,uu____63) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____77 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____79 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____79) in
        if uu____77
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____81 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____81 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____90 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____90
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___99_98  ->
    match uu___99_98 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____100);
        FStar_Syntax_Syntax.tk = uu____101;
        FStar_Syntax_Syntax.pos = uu____102;
        FStar_Syntax_Syntax.vars = uu____103;_} -> uv
    | uu____140 -> failwith "Impossible"
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
          let uu____169 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____169 with
          | FStar_Pervasives_Native.Some (uu____194::(tm,uu____196)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____266 ->
              let uu____279 = new_uvar_aux env k in
              (match uu____279 with
               | (t,u) ->
                   let g =
                     let uu___119_299 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____300 =
                       let uu____315 =
                         let uu____328 = as_uvar u in
                         (reason, env, uu____328, t, k, r) in
                       [uu____315] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_299.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_299.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_299.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____300
                     } in
                   let uu____353 =
                     let uu____360 =
                       let uu____365 = as_uvar u in (uu____365, r) in
                     [uu____360] in
                   (t, uu____353, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____395 =
        let uu____396 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____396 in
      if uu____395
      then
        let us =
          let uu____402 =
            let uu____405 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____423  ->
                 match uu____423 with
                 | (x,uu____429) -> FStar_Syntax_Print.uvar_to_string x)
              uu____405 in
          FStar_All.pipe_right uu____402 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____436 =
            let uu____437 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____437 in
          FStar_Errors.err r uu____436);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____451 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____451 with
    | FStar_Pervasives_Native.None  ->
        let uu____456 =
          let uu____457 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____458 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____457 uu____458 in
        failwith uu____456
    | FStar_Pervasives_Native.Some tk -> tk
let force_sort s =
  let uu____481 =
    let uu____486 = force_sort' s in FStar_Syntax_Syntax.mk uu____486 in
  uu____481 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____504  ->
      match uu____504 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____514;
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
                   let uu____564 =
                     let uu____565 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____565.FStar_Syntax_Syntax.n in
                   match uu____564 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____574 = FStar_Syntax_Util.type_u () in
                       (match uu____574 with
                        | (k,uu____584) ->
                            let t2 =
                              let uu____586 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____586
                                FStar_Pervasives_Native.fst in
                            ((let uu___120_596 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_596.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_596.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____597 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____634) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____645) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____734) ->
                       let uu____759 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____819  ->
                                 fun uu____820  ->
                                   match (uu____819, uu____820) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____898 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____898 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____759 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____1010 = aux must_check_ty1 scope body in
                            (match uu____1010 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____1039 =
                                         FStar_Options.ml_ish () in
                                       if uu____1039
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____1048 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____1048
                                   then
                                     let uu____1049 =
                                       FStar_Range.string_of_range r in
                                     let uu____1050 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____1051 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____1049 uu____1050 uu____1051
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____1065 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____1079 =
                            let uu____1084 =
                              let uu____1085 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____1085
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____1084 in
                          (uu____1079, false)) in
                 let uu____1098 =
                   let uu____1107 = t_binders env in aux false uu____1107 e in
                 match uu____1098 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1136 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____1136
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1142 =
                                let uu____1143 =
                                  let uu____1148 =
                                    let uu____1149 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____1149 in
                                  (uu____1148, rng) in
                                FStar_Errors.Error uu____1143 in
                              raise uu____1142)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1161 ->
               let uu____1162 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1162 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1268) ->
              let uu____1277 = FStar_Syntax_Util.type_u () in
              (match uu____1277 with
               | (k,uu____1301) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_1304 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_1304.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_1304.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____1305 =
                     let uu____1310 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____1310 t in
                   (match uu____1305 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_1334 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___122_1334.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1344 = FStar_Syntax_Util.type_u () in
              (match uu____1344 with
               | (t,uu____1368) ->
                   let x1 =
                     let uu___123_1370 = x in
                     let uu____1371 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_1370.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_1370.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1371
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
              let uu____1394 = FStar_Syntax_Util.type_u () in
              (match uu____1394 with
               | (t,uu____1418) ->
                   let x1 =
                     let uu___124_1420 = x in
                     let uu____1421 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_1420.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_1420.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1421
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1460 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1587  ->
                        fun uu____1588  ->
                          match (uu____1587, uu____1588) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1777 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1777 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____1460 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1977 =
                       let uu____1982 =
                         let uu____1983 =
                           let uu____1992 =
                             let uu____1997 =
                               let uu____1998 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1999 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1998
                                 uu____1999 in
                             uu____1997 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1992,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1983 in
                       FStar_Syntax_Syntax.mk uu____1982 in
                     uu____1977 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____2014 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____2025 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____2036 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____2014, uu____2025, uu____2036, env2, e,
                     (let uu___125_2060 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___125_2060.FStar_Syntax_Syntax.p)
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
                  (fun uu____2144  ->
                     match uu____2144 with
                     | (p2,imp) ->
                         let uu____2163 = elaborate_pat env1 p2 in
                         (uu____2163, imp)) pats in
              let uu____2168 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____2168 with
               | (uu____2175,t) ->
                   let uu____2177 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____2177 with
                    | (f,uu____2195) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____2321::uu____2322) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____2373::uu____2374,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____2452  ->
                                      match uu____2452 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____2479 =
                                                   let uu____2482 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____2482 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____2479
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____2484 =
                                                 maybe_dot inaccessible a r in
                                               (uu____2484, true)
                                           | uu____2489 ->
                                               let uu____2492 =
                                                 let uu____2493 =
                                                   let uu____2498 =
                                                     let uu____2499 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2499 in
                                                   (uu____2498,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____2493 in
                                               raise uu____2492)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____2573,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____2574))
                                   when p_imp ->
                                   let uu____2577 = aux formals' pats' in
                                   (p2, true) :: uu____2577
                               | (uu____2594,FStar_Pervasives_Native.Some
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
                                   let uu____2602 = aux formals' pats2 in
                                   (p3, true) :: uu____2602
                               | (uu____2619,imp) ->
                                   let uu____2625 =
                                     let uu____2632 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____2632) in
                                   let uu____2635 = aux formals' pats' in
                                   uu____2625 :: uu____2635) in
                        let uu___126_2650 = p1 in
                        let uu____2653 =
                          let uu____2654 =
                            let uu____2667 = aux f pats1 in (fv, uu____2667) in
                          FStar_Syntax_Syntax.Pat_cons uu____2654 in
                        {
                          FStar_Syntax_Syntax.v = uu____2653;
                          FStar_Syntax_Syntax.p =
                            (uu___126_2650.FStar_Syntax_Syntax.p)
                        }))
          | uu____2684 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____2718 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____2718 with
          | (b,a,w,env2,arg,p3) ->
              let uu____2771 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____2771 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____2795 =
                     let uu____2796 =
                       let uu____2801 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____2801, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____2796 in
                   raise uu____2795
               | uu____2818 -> (b, a, w, arg, p3)) in
        let uu____2827 = one_pat true env p in
        match uu____2827 with
        | (b,uu____2853,uu____2854,tm,p1) -> (b, tm, p1)
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
          | (uu____2902,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2904)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2913,FStar_Syntax_Syntax.Tm_constant uu____2914) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2918 =
                    let uu____2919 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2920 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2919 uu____2920 in
                  failwith uu____2918)
               else ();
               (let uu____2923 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2923
                then
                  let uu____2924 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2925 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2924
                    uu____2925
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_2929 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_2929.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_2929.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2933 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2933
                then
                  let uu____2934 =
                    let uu____2935 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2936 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2935 uu____2936 in
                  failwith uu____2934
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_2940 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_2940.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_2940.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2942),uu____2943) ->
              let s = force_sort e1 in
              let x1 =
                let uu___129_2958 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___129_2958.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___129_2958.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2976 =
                  let uu____2977 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2977 in
                if uu____2976
                then
                  let uu____2978 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2978
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____2997;
                FStar_Syntax_Syntax.pos = uu____2998;
                FStar_Syntax_Syntax.vars = uu____2999;_},args))
              ->
              ((let uu____3046 =
                  let uu____3047 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3047 Prims.op_Negation in
                if uu____3046
                then
                  let uu____3048 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3048
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3194)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3279) ->
                           let x =
                             let uu____3309 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____3309 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3327) ->
                           let pat =
                             let uu____3355 = aux argpat e2 in
                             let uu____3356 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3355, uu____3356) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3361 ->
                      let uu____3386 =
                        let uu____3387 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3388 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3387 uu____3388 in
                      failwith uu____3386 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____3400;
                     FStar_Syntax_Syntax.pos = uu____3401;
                     FStar_Syntax_Syntax.vars = uu____3402;_},uu____3403);
                FStar_Syntax_Syntax.tk = uu____3404;
                FStar_Syntax_Syntax.pos = uu____3405;
                FStar_Syntax_Syntax.vars = uu____3406;_},args))
              ->
              ((let uu____3461 =
                  let uu____3462 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3462 Prims.op_Negation in
                if uu____3461
                then
                  let uu____3463 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3463
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3609)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3694) ->
                           let x =
                             let uu____3724 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____3724 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3742) ->
                           let pat =
                             let uu____3770 = aux argpat e2 in
                             let uu____3771 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3770, uu____3771) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3776 ->
                      let uu____3801 =
                        let uu____3802 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3803 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3802 uu____3803 in
                      failwith uu____3801 in
                match_args [] args argpats))
          | uu____3812 ->
              let uu____3817 =
                let uu____3818 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3819 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3820 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3818 uu____3819 uu____3820 in
              failwith uu____3817 in
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
    let pat_as_arg uu____3858 =
      match uu____3858 with
      | (p,i) ->
          let uu____3875 = decorated_pattern_as_term p in
          (match uu____3875 with
           | (vars,te) ->
               let uu____3898 =
                 let uu____3903 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3903) in
               (vars, uu____3898)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3917 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3917)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3921 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3921)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3925 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3925)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3946 =
          let uu____3961 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3961 FStar_List.unzip in
        (match uu____3946 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____4071 =
               let uu____4072 =
                 let uu____4073 =
                   let uu____4092 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____4092, args) in
                 FStar_Syntax_Syntax.Tm_app uu____4073 in
               mk1 uu____4072 in
             (vars1, uu____4071))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                    FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term',
                                                                 FStar_Syntax_Syntax.term')
                                                                 FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4143)::[] -> wp
      | uu____4168 ->
          let uu____4179 =
            let uu____4180 =
              let uu____4181 =
                FStar_List.map
                  (fun uu____4191  ->
                     match uu____4191 with
                     | (x,uu____4197) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____4181 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4180 in
          failwith uu____4179 in
    let uu____4204 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____4204, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4225 = destruct_comp c in
        match uu____4225 with
        | (u,uu____4233,wp) ->
            let uu____4235 =
              let uu____4246 =
                let uu____4247 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____4247 in
              [uu____4246] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4235;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4260 =
          let uu____4267 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____4268 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____4267 uu____4268 in
        match uu____4260 with | (m,uu____4270,uu____4271) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4284 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____4284
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
        let uu____4324 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4324 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4361 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4361 with
             | (a,kwp) ->
                 let uu____4392 = destruct_comp m1 in
                 let uu____4399 = destruct_comp m2 in
                 ((md, a, kwp), uu____4392, uu____4399))
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
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____4474 =
              let uu____4475 =
                let uu____4486 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4486] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4475;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4474
let mk_comp:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
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
      let uu___130_4538 = lc in
      let uu____4539 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___130_4538.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4539;
        FStar_Syntax_Syntax.cflags =
          (uu___130_4538.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4546  ->
             let uu____4547 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4547)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4552 =
      let uu____4553 = FStar_Syntax_Subst.compress t in
      uu____4553.FStar_Syntax_Syntax.n in
    match uu____4552 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4558 -> true
    | uu____4573 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4590 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4590
        then c
        else
          (let uu____4592 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4592
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4635 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4635] in
                       let us =
                         let uu____4639 =
                           let uu____4642 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4642] in
                         u_res :: uu____4639 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4648 =
                         let uu____4649 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4650 =
                           let uu____4651 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4652 =
                             let uu____4655 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4656 =
                               let uu____4659 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4659] in
                             uu____4655 :: uu____4656 in
                           uu____4651 :: uu____4652 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4649 uu____4650 in
                       uu____4648 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4663 = destruct_comp c1 in
              match uu____4663 with
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
        let close1 uu____4694 =
          let uu____4695 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4695 in
        let uu___131_4696 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_4696.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_4696.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_4696.FStar_Syntax_Syntax.cflags);
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
          let uu____4710 =
            let uu____4711 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4711 in
          if uu____4710
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4716 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4716
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4718 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4718 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____4726 =
                        let uu____4727 =
                          let uu____4728 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____4729 =
                            let uu____4730 = FStar_Syntax_Syntax.as_arg t in
                            let uu____4731 =
                              let uu____4734 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____4734] in
                            uu____4730 :: uu____4731 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4728 uu____4729 in
                        uu____4727
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____4726) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____4738 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4738
         then
           let uu____4739 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4740 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4741 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4739
             uu____4740 uu____4741
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
          fun uu____4764  ->
            match uu____4764 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4777 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4777
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4780 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4782 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4783 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4780 uu____4782 bstr uu____4783
                  else ());
                 (let bind_it uu____4788 =
                    let uu____4789 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4789
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4803 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4803
                        then
                          let uu____4804 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4806 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4807 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4808 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4809 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4804 uu____4806 uu____4807 uu____4808
                            uu____4809
                        else ());
                       (let try_simplify uu____4826 =
                          let aux uu____4842 =
                            let uu____4843 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4843
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4880 ->
                                  let uu____4881 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4881
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4916 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4916
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4980 =
                                  let uu____4985 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4985, reason) in
                                FStar_Util.Inl uu____4980
                            | uu____4990 -> aux () in
                          let rec maybe_close t x c =
                            let uu____5009 =
                              let uu____5010 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____5010.FStar_Syntax_Syntax.n in
                            match uu____5009 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____5016) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____5026 -> c in
                          let uu____5027 =
                            let uu____5028 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____5028 in
                          if uu____5027
                          then
                            let uu____5043 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____5043
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____5069 =
                                  let uu____5070 =
                                    let uu____5075 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____5075) in
                                  FStar_Errors.Error uu____5070 in
                                raise uu____5069))
                          else
                            (let uu____5089 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____5089
                             then subst_c2 "both total"
                             else
                               (let uu____5103 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____5103
                                then
                                  let uu____5116 =
                                    let uu____5121 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____5121, "both gtot") in
                                  FStar_Util.Inl uu____5116
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____5149 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____5151 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____5151) in
                                       if uu____5149
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___132_5166 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___132_5166.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___132_5166.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____5167 =
                                           let uu____5172 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____5172, "c1 Tot") in
                                         FStar_Util.Inl uu____5167
                                       else aux ()
                                   | uu____5178 -> aux ()))) in
                        let uu____5187 = try_simplify () in
                        match uu____5187 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____5219 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____5219
                              then
                                let uu____5220 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____5221 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____5222 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____5220 uu____5221 uu____5222
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____5233 = lift_and_destruct env c1 c2 in
                            (match uu____5233 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5290 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____5290]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____5292 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____5292] in
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
                                   let uu____5309 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____5310 =
                                     let uu____5313 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____5314 =
                                       let uu____5317 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____5318 =
                                         let uu____5321 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____5322 =
                                           let uu____5325 =
                                             let uu____5326 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____5326 in
                                           [uu____5325] in
                                         uu____5321 :: uu____5322 in
                                       uu____5317 :: uu____5318 in
                                     uu____5313 :: uu____5314 in
                                   uu____5309 :: uu____5310 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____5333 =
                                     let uu____5334 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____5334
                                       wp_args in
                                   uu____5333 FStar_Pervasives_Native.None
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
    FStar_Range.range ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
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
              let uu____5381 =
                let uu____5382 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____5382 in
              if uu____5381
              then f
              else (let uu____5384 = reason1 () in label uu____5384 r f)
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
            let uu___133_5398 = g in
            let uu____5399 =
              let uu____5400 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____5400 in
            {
              FStar_TypeChecker_Env.guard_f = uu____5399;
              FStar_TypeChecker_Env.deferred =
                (uu___133_5398.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_5398.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_5398.FStar_TypeChecker_Env.implicits)
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
      | uu____5412 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5436 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5442 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5442
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5453 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5453
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5460 = destruct_comp c1 in
                    match uu____5460 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5480 =
                            let uu____5481 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5482 =
                              let uu____5483 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5484 =
                                let uu____5487 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5488 =
                                  let uu____5491 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5491] in
                                uu____5487 :: uu____5488 in
                              uu____5483 :: uu____5484 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5481
                              uu____5482 in
                          uu____5480 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___134_5494 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___134_5494.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___134_5494.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___134_5494.FStar_Syntax_Syntax.cflags);
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
            let uu____5532 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5532
            then (lc, g0)
            else
              ((let uu____5539 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5539
                then
                  let uu____5540 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5541 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5540 uu____5541
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_5551  ->
                          match uu___100_5551 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5554 -> [])) in
                let strengthen uu____5562 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5574 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5574 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5585 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5587 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5587) in
                           if uu____5585
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5598 =
                                 let uu____5599 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5599 in
                               FStar_Syntax_Util.comp_set_flags uu____5598
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5605 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5605
                           then
                             let uu____5606 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5607 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5606 uu____5607
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5610 = destruct_comp c2 in
                           match uu____5610 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5630 =
                                   let uu____5631 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5632 =
                                     let uu____5633 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5634 =
                                       let uu____5637 =
                                         let uu____5638 =
                                           let uu____5639 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5639 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5638 in
                                       let uu____5640 =
                                         let uu____5643 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5643] in
                                       uu____5637 :: uu____5640 in
                                     uu____5633 :: uu____5634 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5631
                                     uu____5632 in
                                 uu____5630 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5647 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5647
                                 then
                                   let uu____5648 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5648
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5651 =
                  let uu___135_5652 = lc in
                  let uu____5653 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5654 =
                    let uu____5657 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5659 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5659) in
                    if uu____5657 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5653;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___135_5652.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5654;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5651,
                  (let uu___136_5664 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___136_5664.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___136_5664.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___136_5664.FStar_TypeChecker_Env.implicits)
                   }))))
let add_equality_to_post_condition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun comp  ->
      fun res_t  ->
        let md_pure =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid in
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let y = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____5684 =
          let uu____5689 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5690 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5689, uu____5690) in
        match uu____5684 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5703 =
                let uu____5704 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5705 =
                  let uu____5706 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5707 =
                    let uu____5710 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5710] in
                  uu____5706 :: uu____5707 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5704 uu____5705 in
              uu____5703 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5718 =
                let uu____5719 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5720 =
                  let uu____5721 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5722 =
                    let uu____5725 =
                      let uu____5726 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5726 in
                    let uu____5727 =
                      let uu____5730 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5730] in
                    uu____5725 :: uu____5727 in
                  uu____5721 :: uu____5722 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5719 uu____5720 in
              uu____5718 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5738 =
                let uu____5739 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5740 =
                  let uu____5741 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5742 =
                    let uu____5745 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5746 =
                      let uu____5749 =
                        let uu____5750 =
                          let uu____5751 =
                            let uu____5752 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5752] in
                          FStar_Syntax_Util.abs uu____5751 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5750 in
                      [uu____5749] in
                    uu____5745 :: uu____5746 in
                  uu____5741 :: uu____5742 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5739 uu____5740 in
              uu____5738 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5761 = FStar_TypeChecker_Env.get_range env in
              bind uu____5761 env FStar_Pervasives_Native.None
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
          let comp uu____5784 =
            let uu____5785 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5785
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5788 =
                 let uu____5813 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5814 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5813 uu____5814 in
               match uu____5788 with
               | ((md,uu____5816,uu____5817),(u_res_t,res_t,wp_then),
                  (uu____5821,uu____5822,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5862 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5863 =
                       let uu____5864 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5865 =
                         let uu____5866 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5867 =
                           let uu____5870 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5871 =
                             let uu____5874 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5875 =
                               let uu____5878 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5878] in
                             uu____5874 :: uu____5875 in
                           uu____5870 :: uu____5871 in
                         uu____5866 :: uu____5867 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5864 uu____5865 in
                     uu____5863 FStar_Pervasives_Native.None uu____5862 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5886 =
                     let uu____5887 = FStar_Options.split_cases () in
                     uu____5887 > (Prims.parse_int "0") in
                   if uu____5886
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5895 =
                          let uu____5896 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5897 =
                            let uu____5898 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5899 =
                              let uu____5902 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5902] in
                            uu____5898 :: uu____5899 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5896 uu____5897 in
                        uu____5895 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5905 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5905;
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
      let uu____5914 =
        let uu____5915 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5915 in
      FStar_Syntax_Syntax.fvar uu____5914 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5950  ->
                 match uu____5950 with
                 | (uu____5955,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5960 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5962 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5962
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5984 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5985 =
                 let uu____5986 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5987 =
                   let uu____5988 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5989 =
                     let uu____5992 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5993 =
                       let uu____5996 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5997 =
                         let uu____6000 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____6000] in
                       uu____5996 :: uu____5997 in
                     uu____5992 :: uu____5993 in
                   uu____5988 :: uu____5989 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5986 uu____5987 in
               uu____5985 FStar_Pervasives_Native.None uu____5984 in
             let default_case =
               let post_k =
                 let uu____6009 =
                   let uu____6016 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____6016] in
                 let uu____6017 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____6009 uu____6017 in
               let kwp =
                 let uu____6027 =
                   let uu____6034 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____6034] in
                 let uu____6035 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____6027 uu____6035 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____6042 =
                   let uu____6043 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____6043] in
                 let uu____6044 =
                   let uu____6045 =
                     let uu____6048 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____6048 in
                   let uu____6049 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____6045 uu____6049 in
                 FStar_Syntax_Util.abs uu____6042 uu____6044
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
                 (fun uu____6075  ->
                    fun celse  ->
                      match uu____6075 with
                      | (g,cthen) ->
                          let uu____6083 =
                            let uu____6108 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____6108 celse in
                          (match uu____6083 with
                           | ((md,uu____6110,uu____6111),(uu____6112,uu____6113,wp_then),
                              (uu____6115,uu____6116,wp_else)) ->
                               let uu____6136 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____6136 []))
                 lcases default_case in
             let uu____6137 =
               let uu____6138 = FStar_Options.split_cases () in
               uu____6138 > (Prims.parse_int "0") in
             if uu____6137
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____6142 = destruct_comp comp1 in
                match uu____6142 with
                | (uu____6149,uu____6150,wp) ->
                    let wp1 =
                      let uu____6157 =
                        let uu____6158 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____6159 =
                          let uu____6160 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____6161 =
                            let uu____6164 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____6164] in
                          uu____6160 :: uu____6161 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____6158 uu____6159 in
                      uu____6157 FStar_Pervasives_Native.None
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
          let uu____6182 =
            ((let uu____6185 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____6185) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____6187 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____6187) in
          if uu____6182
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____6198 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____6204 =
            (let uu____6207 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____6207) || env.FStar_TypeChecker_Env.lax in
          if uu____6204
          then c
          else
            (let uu____6213 = FStar_Syntax_Util.is_partial_return c in
             if uu____6213
             then c
             else
               (let uu____6219 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____6219
                then
                  let uu____6224 =
                    let uu____6225 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____6225 in
                  (if uu____6224
                   then
                     let uu____6230 =
                       let uu____6231 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____6232 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____6231 uu____6232 in
                     failwith uu____6230
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____6239 =
                        let uu____6240 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____6240 in
                      if uu____6239
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___137_6247 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___137_6247.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___137_6247.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___137_6247.FStar_Syntax_Syntax.effect_args);
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
                     let uu____6260 =
                       let uu____6265 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____6265
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____6260 in
                   let eq1 =
                     let uu____6271 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____6271 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____6273 =
                     let uu____6274 =
                       let uu____6281 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____6281.FStar_Syntax_Syntax.comp in
                     uu____6274 () in
                   FStar_Syntax_Util.comp_set_flags uu____6273 flags))) in
        let uu___138_6284 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___138_6284.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___138_6284.FStar_Syntax_Syntax.res_typ);
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
          let uu____6313 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6313 with
          | FStar_Pervasives_Native.None  ->
              let uu____6322 =
                let uu____6323 =
                  let uu____6328 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____6329 = FStar_TypeChecker_Env.get_range env in
                  (uu____6328, uu____6329) in
                FStar_Errors.Error uu____6323 in
              raise uu____6322
          | FStar_Pervasives_Native.Some g -> (e, c', g)
let maybe_coerce_bool_to_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
            let uu____6366 =
              let uu____6367 = FStar_Syntax_Subst.compress t2 in
              uu____6367.FStar_Syntax_Syntax.n in
            match uu____6366 with
            | FStar_Syntax_Syntax.Tm_type uu____6372 -> true
            | uu____6373 -> false in
          let uu____6374 =
            let uu____6375 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____6375.FStar_Syntax_Syntax.n in
          match uu____6374 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6385 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6396 =
                  let uu____6397 =
                    let uu____6398 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6398 in
                  (FStar_Pervasives_Native.None, uu____6397) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6396 in
              let e1 =
                let uu____6414 =
                  let uu____6415 =
                    let uu____6416 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6416] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6415 in
                uu____6414
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6423 -> (e, lc)
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
              (let uu____6456 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6456 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6479 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6501 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6501, false)
            else
              (let uu____6507 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6507, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6518) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___139_6523 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___139_6523.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___139_6523.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___139_6523.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6528 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6528 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_6536 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_6536.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_6536.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___140_6536.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_6539 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_6539.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_6539.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_6539.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6547 =
                     let uu____6548 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6548
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6555 =
                          let uu____6556 = FStar_Syntax_Subst.compress f1 in
                          uu____6556.FStar_Syntax_Syntax.n in
                        match uu____6555 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6565,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____6567;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6568;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6569;_},uu____6570)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_6596 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_6596.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_6596.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___142_6596.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6597 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6604 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6604
                              then
                                let uu____6605 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6606 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6607 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6608 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6605 uu____6606 uu____6607 uu____6608
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6611 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6611 with
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
                                  let uu____6626 = destruct_comp ct in
                                  (match uu____6626 with
                                   | (u_t,uu____6638,uu____6639) ->
                                       let wp =
                                         let uu____6645 =
                                           let uu____6646 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6647 =
                                             let uu____6648 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6649 =
                                               let uu____6652 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6652] in
                                             uu____6648 :: uu____6649 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6646 uu____6647 in
                                         uu____6645
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6656 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6656 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6674 =
                                             let uu____6675 =
                                               let uu____6676 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6676] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6675 in
                                           uu____6674
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6680 =
                                         let uu____6685 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6698 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6699 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6685
                                           uu____6698 e cret uu____6699 in
                                       (match uu____6680 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___143_6707 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___143_6707.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___143_6707.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6709 =
                                                let uu____6710 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6710 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6709
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6727 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6727
                                              then
                                                let uu____6728 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6728
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_6738  ->
                             match uu___101_6738 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6741 -> [])) in
                   let lc1 =
                     let uu___144_6743 = lc in
                     let uu____6744 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6744;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___145_6746 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___145_6746.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___145_6746.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___145_6746.FStar_TypeChecker_Env.implicits)
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
        let uu____6773 =
          let uu____6774 =
            let uu____6775 =
              let uu____6776 =
                let uu____6777 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6777 in
              [uu____6776] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6775 in
          uu____6774 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6773 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6784 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6784
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6804 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6821 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6852)::(ens,uu____6854)::uu____6855 ->
                    let uu____6898 =
                      let uu____6901 = norm req in
                      FStar_Pervasives_Native.Some uu____6901 in
                    let uu____6902 =
                      let uu____6903 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____6903 in
                    (uu____6898, uu____6902)
                | uu____6906 ->
                    let uu____6917 =
                      let uu____6918 =
                        let uu____6923 =
                          let uu____6924 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6924 in
                        (uu____6923, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6918 in
                    raise uu____6917)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6940)::uu____6941 ->
                    let uu____6968 =
                      let uu____6973 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6973 in
                    (match uu____6968 with
                     | (us_r,uu____7005) ->
                         let uu____7006 =
                           let uu____7011 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7011 in
                         (match uu____7006 with
                          | (us_e,uu____7043) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____7046 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7046
                                  us_r in
                              let as_ens =
                                let uu____7048 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7048
                                  us_e in
                              let req =
                                let uu____7054 =
                                  let uu____7055 =
                                    let uu____7056 =
                                      let uu____7069 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____7069] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7056 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7055 in
                                uu____7054
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____7093 =
                                  let uu____7094 =
                                    let uu____7095 =
                                      let uu____7108 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____7108] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7095 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7094 in
                                uu____7093 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____7127 =
                                let uu____7130 = norm req in
                                FStar_Pervasives_Native.Some uu____7130 in
                              let uu____7131 =
                                let uu____7132 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____7132 in
                              (uu____7127, uu____7131)))
                | uu____7135 -> failwith "Impossible"))
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
      (let uu____7167 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____7167
       then
         let uu____7168 = FStar_Syntax_Print.term_to_string tm in
         let uu____7169 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7168 uu____7169
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
        (let uu____7192 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____7192
         then
           let uu____7193 = FStar_Syntax_Print.term_to_string tm in
           let uu____7194 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7193
             uu____7194
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____7200 =
      let uu____7201 =
        let uu____7202 = FStar_Syntax_Subst.compress t in
        uu____7202.FStar_Syntax_Syntax.n in
      match uu____7201 with
      | FStar_Syntax_Syntax.Tm_app uu____7207 -> false
      | uu____7226 -> true in
    if uu____7200
    then t
    else
      (let uu____7228 = FStar_Syntax_Util.head_and_args t in
       match uu____7228 with
       | (head1,args) ->
           let uu____7277 =
             let uu____7278 =
               let uu____7279 = FStar_Syntax_Subst.compress head1 in
               uu____7279.FStar_Syntax_Syntax.n in
             match uu____7278 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7284 -> false in
           if uu____7277
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7314 ->
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
             let uu____7356 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____7356 with
             | (formals,uu____7372) ->
                 let n_implicits =
                   let uu____7394 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7470  ->
                             match uu____7470 with
                             | (uu____7477,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7394 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7608 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7608 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7632 =
                     let uu____7633 =
                       let uu____7638 =
                         let uu____7639 = FStar_Util.string_of_int n_expected in
                         let uu____7646 = FStar_Syntax_Print.term_to_string e in
                         let uu____7647 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7639 uu____7646 uu____7647 in
                       let uu____7654 = FStar_TypeChecker_Env.get_range env in
                       (uu____7638, uu____7654) in
                     FStar_Errors.Error uu____7633 in
                   raise uu____7632
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___102_7675 =
             match uu___102_7675 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7709 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7709 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____7818) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7861,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7894 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7894 with
                           | (v1,uu____7934,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7951 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7951 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8044 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8044)))
                      | (uu____8071,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____8117 =
                      let uu____8144 = inst_n_binders t in
                      aux [] uu____8144 bs1 in
                    (match uu____8117 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8215) -> (e, torig, guard)
                          | (uu____8246,[]) when
                              let uu____8277 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____8277 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8278 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8314 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____8333 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____8342 =
      let uu____8345 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____8345
        (FStar_List.map
           (fun u  ->
              let uu____8355 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____8355 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____8342 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____8374 = FStar_Util.set_is_empty x in
      if uu____8374
      then []
      else
        (let s =
           let uu____8381 =
             let uu____8384 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____8384 in
           FStar_All.pipe_right uu____8381 FStar_Util.set_elements in
         (let uu____8392 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____8392
          then
            let uu____8393 =
              let uu____8394 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8394 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8393
          else ());
         (let r =
            let uu____8401 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8401 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8416 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8416
                     then
                       let uu____8417 =
                         let uu____8418 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8418 in
                       let uu____8419 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8420 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8417 uu____8419 uu____8420
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
        let uu____8444 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8444 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_8485 =
  match uu___103_8485 with
  | FStar_Pervasives_Native.None  -> ts
  | FStar_Pervasives_Native.Some t ->
      let t1 =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          FStar_Range.dummyRange in
      let t2 =
        FStar_Syntax_Subst.close_univ_vars (FStar_Pervasives_Native.fst ts)
          t1 in
      (FStar_ST.write (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.tk
         (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n));
       ts)
let check_universe_generalization:
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____8542) -> generalized_univ_names
        | (uu____8549,[]) -> explicit_univ_names
        | uu____8556 ->
            let uu____8565 =
              let uu____8566 =
                let uu____8571 =
                  let uu____8572 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____8572 in
                (uu____8571, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____8566 in
            raise uu____8565
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                        FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0 in
      let univnames1 = gather_free_univnames env t in
      let univs1 = FStar_Syntax_Free.univs t in
      (let uu____8591 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8591
       then
         let uu____8592 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8592
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8598 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8598
        then
          let uu____8599 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8599
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____8606 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____8606))
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
      let uu____8657 =
        let uu____8658 =
          FStar_Util.for_all
            (fun uu____8670  ->
               match uu____8670 with
               | (uu____8679,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____8658 in
      if uu____8657
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____8717 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____8717
            then
              let uu____8718 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____8718
            else ());
           (let c1 =
              let uu____8721 = FStar_TypeChecker_Env.should_verify env in
              if uu____8721
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
            (let uu____8724 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____8724
             then
               let uu____8725 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8725
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____8798 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____8798 FStar_Util.set_elements in
         let uu____8905 =
           let uu____8944 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____9077  ->
                     match uu____9077 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____9152 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____9152
                           then
                             let uu____9153 =
                               let uu____9154 =
                                 let uu____9157 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____9157
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____9154
                                 (FStar_String.concat ", ") in
                             let uu____9184 =
                               let uu____9185 =
                                 let uu____9188 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____9188
                                   (FStar_List.map
                                      (fun uu____9216  ->
                                         match uu____9216 with
                                         | (u,t2) ->
                                             let uu____9223 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____9224 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____9223 uu____9224)) in
                               FStar_All.pipe_right uu____9185
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____9153 uu____9184
                           else ());
                          (let univs2 =
                             let uu____9231 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____9254  ->
                                    match uu____9254 with
                                    | (uu____9263,t2) ->
                                        let uu____9265 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____9265) univs1 uu____9231 in
                           let uvs = gen_uvars uvt in
                           (let uu____9292 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____9292
                            then
                              let uu____9293 =
                                let uu____9294 =
                                  let uu____9297 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____9297
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____9294
                                  (FStar_String.concat ", ") in
                              let uu____9324 =
                                let uu____9325 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____9361  ->
                                          match uu____9361 with
                                          | (u,t2) ->
                                              let uu____9368 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____9369 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____9368 uu____9369)) in
                                FStar_All.pipe_right uu____9325
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____9293 uu____9324
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____8944 FStar_List.unzip in
         match uu____8905 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____9614 = FStar_List.hd univs1 in
               let uu____9619 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____9639 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____9639
                      then out
                      else
                        (let uu____9643 =
                           let uu____9644 =
                             let uu____9649 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____9649) in
                           FStar_Errors.Error uu____9644 in
                         raise uu____9643)) uu____9614 uu____9619 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____9656 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____9656
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
                      (fun uu____9741  ->
                         match uu____9741 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____9818  ->
                                       match uu____9818 with
                                       | (u,k) ->
                                           let uu____9831 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____9831 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____9841;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9842;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9843;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____9854,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____9856;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9857;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9858;_},uu____9859);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____9860;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9861;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9862;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____9897 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____9904 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____9908 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____9908 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____9952 =
                                                         let uu____9955 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____9955 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____9952 kres in
                                                     let t =
                                                       let uu____9959 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____9959
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____9963 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____9998 ->
                                   let uu____10013 = (e, c) in
                                   (match uu____10013 with
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
                                          let uu____10031 =
                                            let uu____10032 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____10032.FStar_Syntax_Syntax.n in
                                          match uu____10031 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10063 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____10063 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____10080 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____10082 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____10082)) in
                             (match uu____9963 with
                              | (e1,c1) -> (gen_univs1, e1, c1)))) in
               FStar_Pervasives_Native.Some ecs1)))
let generalize:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
        FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____10150 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____10150
       then
         let uu____10151 =
           let uu____10152 =
             FStar_List.map
               (fun uu____10165  ->
                  match uu____10165 with
                  | (lb,uu____10173,uu____10174) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____10152 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____10151
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____10195  ->
              match uu____10195 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____10220 =
           let uu____10233 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____10268  ->
                     match uu____10268 with | (uu____10279,e,c) -> (e, c))) in
           gen env uu____10233 in
         match uu____10220 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____10344  ->
                     match uu____10344 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____10436  ->
                  fun uu____10437  ->
                    match (uu____10436, uu____10437) with
                    | ((l,uu____10501,uu____10502),(us,e,c)) ->
                        ((let uu____10549 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____10549
                          then
                            let uu____10550 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____10551 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____10552 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____10553 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____10550 uu____10551 uu____10552 uu____10553
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____10595  ->
              match uu____10595 with
              | (l,generalized_univs,t,c) ->
                  let uu____10626 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____10626, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____10671 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____10671 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10677 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____10677) in
          let is_var e1 =
            let uu____10684 =
              let uu____10685 = FStar_Syntax_Subst.compress e1 in
              uu____10685.FStar_Syntax_Syntax.n in
            match uu____10684 with
            | FStar_Syntax_Syntax.Tm_name uu____10690 -> true
            | uu____10691 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___146_10711 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___146_10711.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___146_10711.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____10712 ->
                let uu___147_10713 = e2 in
                let uu____10714 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___147_10713.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____10714;
                  FStar_Syntax_Syntax.pos =
                    (uu___147_10713.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___147_10713.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___148_10722 = env1 in
            let uu____10723 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_10722.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_10722.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_10722.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_10722.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_10722.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_10722.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_10722.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_10722.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_10722.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_10722.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_10722.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_10722.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_10722.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_10722.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_10722.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10723;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_10722.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_10722.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_10722.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_10722.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_10722.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_10722.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_10722.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_10722.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___148_10722.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___148_10722.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___148_10722.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____10724 = check env2 t1 t2 in
          match uu____10724 with
          | FStar_Pervasives_Native.None  ->
              let uu____10731 =
                let uu____10732 =
                  let uu____10737 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10738 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10737, uu____10738) in
                FStar_Errors.Error uu____10732 in
              raise uu____10731
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10745 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10745
                then
                  let uu____10746 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10746
                else ());
               (let uu____10748 = decorate e t2 in (uu____10748, g)))
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
        let uu____10783 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10783
        then
          let uu____10788 = discharge g1 in
          let uu____10789 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10788, uu____10789)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10808 =
               let uu____10809 =
                 let uu____10810 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10810 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10809
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10808
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10812 = destruct_comp c1 in
           match uu____10812 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10831 = FStar_TypeChecker_Env.get_range env in
                 let uu____10832 =
                   let uu____10833 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10834 =
                     let uu____10835 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10836 =
                       let uu____10839 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10839] in
                     uu____10835 :: uu____10836 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10833 uu____10834 in
                 uu____10832
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____10831 in
               ((let uu____10843 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10843
                 then
                   let uu____10844 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10844
                 else ());
                (let g2 =
                   let uu____10847 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10847 in
                 let uu____10848 = discharge g2 in
                 let uu____10849 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10848, uu____10849))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_10879 =
        match uu___104_10879 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10889)::[] -> f fst1
        | uu____10914 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10919 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10919
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____10932 =
          let uu____10937 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10937 in
        FStar_All.pipe_right uu____10932
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____10950 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10950
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_10970 =
        match uu___105_10970 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10980)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11007)::[] ->
            let uu____11048 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____11048
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____11057 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____11067 =
          let uu____11074 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____11074) in
        let uu____11079 =
          let uu____11088 =
            let uu____11095 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____11095) in
          let uu____11100 =
            let uu____11109 =
              let uu____11116 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____11116) in
            let uu____11121 =
              let uu____11130 =
                let uu____11137 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____11137) in
              let uu____11142 =
                let uu____11151 =
                  let uu____11158 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____11158) in
                [uu____11151; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____11130 :: uu____11142 in
            uu____11109 :: uu____11121 in
          uu____11088 :: uu____11100 in
        uu____11067 :: uu____11079 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____11209 =
            FStar_Util.find_map table
              (fun uu____11222  ->
                 match uu____11222 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11239 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____11239
                     else FStar_Pervasives_Native.None) in
          (match uu____11209 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11242 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____11247 =
      let uu____11248 = FStar_Syntax_Util.un_uinst l in
      uu____11248.FStar_Syntax_Syntax.n in
    match uu____11247 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11254 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11280)::uu____11281 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11292 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____11299,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11300))::uu____11301 -> bs
      | uu____11318 ->
          let uu____11319 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11319 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11323 =
                 let uu____11324 = FStar_Syntax_Subst.compress t in
                 uu____11324.FStar_Syntax_Syntax.n in
               (match uu____11323 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11330) ->
                    let uu____11351 =
                      FStar_Util.prefix_until
                        (fun uu___106_11391  ->
                           match uu___106_11391 with
                           | (uu____11398,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11399)) ->
                               false
                           | uu____11402 -> true) bs' in
                    (match uu____11351 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11437,uu____11438) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11510,uu____11511) ->
                         let uu____11584 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11602  ->
                                   match uu____11602 with
                                   | (x,uu____11610) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11584
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11657  ->
                                     match uu____11657 with
                                     | (x,i) ->
                                         let uu____11676 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11676, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11686 -> bs))
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
              (let uu____11710 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____11710 e.FStar_Syntax_Syntax.pos)
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
          let uu____11732 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11732
          then e
          else
            (let uu____11734 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____11734
               e.FStar_Syntax_Syntax.pos)
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                      FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____11764 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11764
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11766 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11766))
         else ());
        (let fv =
           let uu____11769 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11769
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
         let uu____11777 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___149_11787 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_11787.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_11787.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_11787.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___149_11787.FStar_Syntax_Syntax.sigattrs)
           }), uu____11777))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_11799 =
        match uu___107_11799 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11800 -> false in
      let reducibility uu___108_11804 =
        match uu___108_11804 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11805 -> false in
      let assumption uu___109_11809 =
        match uu___109_11809 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11810 -> false in
      let reification uu___110_11814 =
        match uu___110_11814 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11815 -> true
        | uu____11816 -> false in
      let inferred uu___111_11820 =
        match uu___111_11820 with
        | FStar_Syntax_Syntax.Discriminator uu____11821 -> true
        | FStar_Syntax_Syntax.Projector uu____11822 -> true
        | FStar_Syntax_Syntax.RecordType uu____11827 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11836 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11845 -> false in
      let has_eq uu___112_11849 =
        match uu___112_11849 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11850 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11910 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11915 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11919 =
        let uu____11920 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_11924  ->
                  match uu___113_11924 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11925 -> false)) in
        FStar_All.pipe_right uu____11920 Prims.op_Negation in
      if uu____11919
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11938 =
            let uu____11939 =
              let uu____11944 =
                let uu____11945 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11945 msg in
              (uu____11944, r) in
            FStar_Errors.Error uu____11939 in
          raise uu____11938 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11953 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11957 =
            let uu____11958 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11958 in
          if uu____11957 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11963),uu____11964) ->
              ((let uu____11980 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11980
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11984 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11984
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11990 ->
              let uu____11999 =
                let uu____12000 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____12000 in
              if uu____11999 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12006 ->
              let uu____12013 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____12013 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12017 ->
              let uu____12024 =
                let uu____12025 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____12025 in
              if uu____12024 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12031 ->
              let uu____12032 =
                let uu____12033 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____12033 in
              if uu____12032 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12039 ->
              let uu____12040 =
                let uu____12041 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____12041 in
              if uu____12040 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12047 ->
              let uu____12060 =
                let uu____12061 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____12061 in
              if uu____12060 then err'1 () else ()
          | uu____12067 -> ()))
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
                          let uu____12144 =
                            let uu____12149 =
                              let uu____12150 =
                                let uu____12159 =
                                  let uu____12160 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____12160 in
                                (uu____12159, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____12150 in
                            FStar_Syntax_Syntax.mk uu____12149 in
                          uu____12144 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____12202  ->
                                  match uu____12202 with
                                  | (x,imp) ->
                                      let uu____12213 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____12213, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____12215 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____12215 in
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
                             let uu____12226 =
                               let uu____12227 =
                                 let uu____12228 =
                                   let uu____12229 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____12230 =
                                     let uu____12231 =
                                       let uu____12232 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____12232 in
                                     [uu____12231] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____12229
                                     uu____12230 in
                                 uu____12228 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____12227 in
                             FStar_Syntax_Util.refine x uu____12226 in
                           let uu____12235 =
                             let uu___150_12236 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_12236.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_12236.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____12235) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____12251 =
                          FStar_List.map
                            (fun uu____12273  ->
                               match uu____12273 with
                               | (x,uu____12285) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____12251 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12334  ->
                                match uu____12334 with
                                | (x,uu____12346) ->
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
                             (let uu____12360 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12360)
                               ||
                               (let uu____12362 =
                                  let uu____12363 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12363.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12362) in
                           let quals =
                             let uu____12367 =
                               let uu____12370 =
                                 let uu____12373 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12373
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12377 =
                                 FStar_List.filter
                                   (fun uu___114_12381  ->
                                      match uu___114_12381 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12382 -> false) iquals in
                               FStar_List.append uu____12370 uu____12377 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12367 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12403 =
                                 let uu____12404 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12404 in
                               FStar_Syntax_Syntax.mk_Total uu____12403 in
                             let uu____12405 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12405 in
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
                           (let uu____12408 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12408
                            then
                              let uu____12409 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12409
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
                                             fun uu____12466  ->
                                               match uu____12466 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12490 =
                                                       let uu____12493 =
                                                         let uu____12494 =
                                                           let uu____12503 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12503,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12494 in
                                                       pos uu____12493 in
                                                     (uu____12490, b)
                                                   else
                                                     (let uu____12507 =
                                                        let uu____12510 =
                                                          let uu____12511 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12511 in
                                                        pos uu____12510 in
                                                      (uu____12507, b)))) in
                                   let pat_true =
                                     let uu____12533 =
                                       let uu____12536 =
                                         let uu____12537 =
                                           let uu____12550 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12550, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12537 in
                                       pos uu____12536 in
                                     (uu____12533,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12594 =
                                       let uu____12597 =
                                         let uu____12598 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12598 in
                                       pos uu____12597 in
                                     (uu____12594,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12616 =
                                     let uu____12621 =
                                       let uu____12622 =
                                         let uu____12651 =
                                           let uu____12654 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12655 =
                                             let uu____12658 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12658] in
                                           uu____12654 :: uu____12655 in
                                         (arg_exp, uu____12651) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12622 in
                                     FStar_Syntax_Syntax.mk uu____12621 in
                                   uu____12616 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12666 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12666
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
                                let uu____12674 =
                                  let uu____12679 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12679 in
                                let uu____12680 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12674;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12680
                                } in
                              let impl =
                                let uu____12686 =
                                  let uu____12687 =
                                    let uu____12694 =
                                      let uu____12697 =
                                        let uu____12698 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12698
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12697] in
                                    ((false, [lb]), uu____12694) in
                                  FStar_Syntax_Syntax.Sig_let uu____12687 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12686;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12716 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12716
                               then
                                 let uu____12717 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12717
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
                                fun uu____12759  ->
                                  match uu____12759 with
                                  | (a,uu____12765) ->
                                      let uu____12766 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12766 with
                                       | (field_name,uu____12772) ->
                                           let field_proj_tm =
                                             let uu____12774 =
                                               let uu____12775 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12775 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12774 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12796 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12827  ->
                                    match uu____12827 with
                                    | (x,uu____12835) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12837 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12837 with
                                         | (field_name,uu____12845) ->
                                             let t =
                                               let uu____12847 =
                                                 let uu____12848 =
                                                   let uu____12853 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12853 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12848 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12847 in
                                             let only_decl =
                                               (let uu____12857 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12857)
                                                 ||
                                                 (let uu____12859 =
                                                    let uu____12860 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12860.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12859) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12874 =
                                                   FStar_List.filter
                                                     (fun uu___115_12878  ->
                                                        match uu___115_12878
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12879 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12874
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_12892  ->
                                                         match uu___116_12892
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12893 ->
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
                                             ((let uu____12896 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12896
                                               then
                                                 let uu____12897 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12897
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
                                                           fun uu____12945 
                                                             ->
                                                             match uu____12945
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12969
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12969,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12985
                                                                    =
                                                                    let uu____12988
                                                                    =
                                                                    let uu____12989
                                                                    =
                                                                    let uu____12998
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12998,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12989 in
                                                                    pos
                                                                    uu____12988 in
                                                                    (uu____12985,
                                                                    b))
                                                                   else
                                                                    (let uu____13002
                                                                    =
                                                                    let uu____13005
                                                                    =
                                                                    let uu____13006
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____13006 in
                                                                    pos
                                                                    uu____13005 in
                                                                    (uu____13002,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____13024 =
                                                     let uu____13027 =
                                                       let uu____13028 =
                                                         let uu____13041 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____13041,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____13028 in
                                                     pos uu____13027 in
                                                   let uu____13050 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____13024,
                                                     FStar_Pervasives_Native.None,
                                                     uu____13050) in
                                                 let body =
                                                   let uu____13068 =
                                                     let uu____13073 =
                                                       let uu____13074 =
                                                         let uu____13103 =
                                                           let uu____13106 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____13106] in
                                                         (arg_exp,
                                                           uu____13103) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____13074 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13073 in
                                                   uu____13068
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____13115 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____13115
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
                                                   let uu____13122 =
                                                     let uu____13127 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____13127 in
                                                   let uu____13128 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____13122;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____13128
                                                   } in
                                                 let impl =
                                                   let uu____13134 =
                                                     let uu____13135 =
                                                       let uu____13142 =
                                                         let uu____13145 =
                                                           let uu____13146 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____13146
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____13145] in
                                                       ((false, [lb]),
                                                         uu____13142) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____13135 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____13134;
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
                                                 (let uu____13164 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____13164
                                                  then
                                                    let uu____13165 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____13165
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12796 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____13209) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____13214 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____13214 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____13236 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____13236 with
                    | (formals,uu____13254) ->
                        let uu____13275 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____13307 =
                                   let uu____13308 =
                                     let uu____13309 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____13309 in
                                   FStar_Ident.lid_equals typ_lid uu____13308 in
                                 if uu____13307
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____13328,uvs',tps,typ0,uu____13332,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____13351 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____13275 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13426 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13426 with
                              | (indices,uu____13444) ->
                                  let refine_domain =
                                    let uu____13466 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_13471  ->
                                              match uu___117_13471 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13472 -> true
                                              | uu____13481 -> false)) in
                                    if uu____13466
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_13489 =
                                      match uu___118_13489 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13492,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13504 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13505 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13505 with
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
                                    let uu____13516 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13516 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13581  ->
                                               fun uu____13582  ->
                                                 match (uu____13581,
                                                         uu____13582)
                                                 with
                                                 | ((x,uu____13600),(x',uu____13602))
                                                     ->
                                                     let uu____13611 =
                                                       let uu____13620 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13620) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13611) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13621 -> []