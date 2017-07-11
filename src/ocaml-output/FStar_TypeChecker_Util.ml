open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____14 = FStar_TypeChecker_Env.get_range env in
      let uu____15 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____14 uu____15
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____20 =
      let uu____21 = FStar_Syntax_Subst.compress t in
      uu____21.FStar_Syntax_Syntax.n in
    match uu____20 with
    | FStar_Syntax_Syntax.Tm_type uu____23 -> true
    | uu____24 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____32 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____32
      (FStar_List.filter
         (fun uu____41  ->
            match uu____41 with
            | (x,uu____45) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____57 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____59 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____59) in
        if uu____57
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____61 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____61 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____70 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____70
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___98_76  ->
    match uu___98_76 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____78);
        FStar_Syntax_Syntax.pos = uu____79;
        FStar_Syntax_Syntax.vars = uu____80;_} -> uv
    | uu____94 -> failwith "Impossible"
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
          let uu____117 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____117 with
          | FStar_Pervasives_Native.Some (uu____129::(tm,uu____131)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____161 ->
              let uu____167 = new_uvar_aux env k in
              (match uu____167 with
               | (t,u) ->
                   let g =
                     let uu___117_179 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____180 =
                       let uu____188 =
                         let uu____195 = as_uvar u in
                         (reason, env, uu____195, t, k, r) in
                       [uu____188] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___117_179.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___117_179.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___117_179.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____180
                     } in
                   let uu____208 =
                     let uu____212 =
                       let uu____215 = as_uvar u in (uu____215, r) in
                     [uu____212] in
                   (t, uu____208, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____235 =
        let uu____236 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____236 in
      if uu____235
      then
        let us =
          let uu____240 =
            let uu____242 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____253  ->
                 match uu____253 with
                 | (x,uu____257) -> FStar_Syntax_Print.uvar_to_string x)
              uu____242 in
          FStar_All.pipe_right uu____240 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____263 =
            let uu____264 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____264 in
          FStar_Errors.err r uu____263);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____276  ->
      match uu____276 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____283;
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
                   let uu____313 =
                     let uu____314 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____314.FStar_Syntax_Syntax.n in
                   match uu____313 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____318 = FStar_Syntax_Util.type_u () in
                       (match uu____318 with
                        | (k,uu____324) ->
                            let t2 =
                              let uu____326 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____326
                                FStar_Pervasives_Native.fst in
                            ((let uu___118_332 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_332.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_332.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____333 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____358) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____363) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____396) ->
                       let uu____407 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____444  ->
                                 fun uu____445  ->
                                   match (uu____444, uu____445) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____487 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____487 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____407 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____548 = aux must_check_ty1 scope body in
                            (match uu____548 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____565 =
                                         FStar_Options.ml_ish () in
                                       if uu____565
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____571 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____571
                                   then
                                     let uu____572 =
                                       FStar_Range.string_of_range r in
                                     let uu____573 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____574 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____572 uu____573 uu____574
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____580 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____588 =
                            let uu____591 =
                              let uu____592 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____592
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____591 in
                          (uu____588, false)) in
                 let uu____599 =
                   let uu____604 = t_binders env in aux false uu____604 e in
                 match uu____599 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____619 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____619
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____622 =
                                let uu____623 =
                                  let uu____626 =
                                    let uu____627 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____627 in
                                  (uu____626, rng) in
                                FStar_Errors.Error uu____623 in
                              raise uu____622)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____632 ->
               let uu____633 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____633 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____701) ->
              let uu____704 = FStar_Syntax_Util.type_u () in
              (match uu____704 with
               | (k,uu____717) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_720 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_720.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_720.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____721 =
                     let uu____724 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____724 t in
                   (match uu____721 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_738 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___120_738.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____744 = FStar_Syntax_Util.type_u () in
              (match uu____744 with
               | (t,uu____757) ->
                   let x1 =
                     let uu___121_759 = x in
                     let uu____760 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_759.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_759.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____760
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
              let uu____774 = FStar_Syntax_Util.type_u () in
              (match uu____774 with
               | (t,uu____787) ->
                   let x1 =
                     let uu___122_789 = x in
                     let uu____790 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_789.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_789.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____790
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____812 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____885  ->
                        fun uu____886  ->
                          match (uu____885, uu____886) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____985 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____985 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____812 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1092 =
                       let uu____1094 =
                         let uu____1095 =
                           let uu____1099 =
                             let uu____1101 =
                               let uu____1102 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1103 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1102
                                 uu____1103 in
                             uu____1101 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1099,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1095 in
                       FStar_Syntax_Syntax.mk uu____1094 in
                     uu____1092 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1117 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1123 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1129 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1117, uu____1123, uu____1129, env2, e,
                     (let uu___123_1141 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___123_1141.FStar_Syntax_Syntax.p)
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
                  (fun uu____1196  ->
                     match uu____1196 with
                     | (p2,imp) ->
                         let uu____1207 = elaborate_pat env1 p2 in
                         (uu____1207, imp)) pats in
              let uu____1210 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1210 with
               | (uu____1214,t) ->
                   let uu____1216 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1216 with
                    | (f,uu____1225) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1290::uu____1291) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1317::uu____1318,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1361  ->
                                      match uu____1361 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1377 =
                                                   let uu____1379 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____1379 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1377
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1381 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1381, true)
                                           | uu____1384 ->
                                               let uu____1386 =
                                                 let uu____1387 =
                                                   let uu____1390 =
                                                     let uu____1391 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1391 in
                                                   (uu____1390,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1387 in
                                               raise uu____1386)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1431,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____1432))
                                   when p_imp ->
                                   let uu____1434 = aux formals' pats' in
                                   (p2, true) :: uu____1434
                               | (uu____1443,FStar_Pervasives_Native.Some
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
                                   let uu____1449 = aux formals' pats2 in
                                   (p3, true) :: uu____1449
                               | (uu____1458,imp) ->
                                   let uu____1462 =
                                     let uu____1466 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1466) in
                                   let uu____1468 = aux formals' pats' in
                                   uu____1462 :: uu____1468) in
                        let uu___124_1476 = p1 in
                        let uu____1478 =
                          let uu____1479 =
                            let uu____1486 = aux f pats1 in (fv, uu____1486) in
                          FStar_Syntax_Syntax.Pat_cons uu____1479 in
                        {
                          FStar_Syntax_Syntax.v = uu____1478;
                          FStar_Syntax_Syntax.p =
                            (uu___124_1476.FStar_Syntax_Syntax.p)
                        }))
          | uu____1495 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1518 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1518 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1548 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1548 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____1561 =
                     let uu____1562 =
                       let uu____1565 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1565, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1562 in
                   raise uu____1561
               | uu____1574 -> (b, a, w, arg, p3)) in
        let uu____1579 = one_pat true env p in
        match uu____1579 with
        | (b,uu____1593,uu____1594,tm,p1) -> (b, tm, p1)
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
          | (uu____1632,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1634)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1637,FStar_Syntax_Syntax.Tm_constant uu____1638) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1642 =
                    let uu____1643 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1644 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1643 uu____1644 in
                  failwith uu____1642)
               else ();
               (let uu____1647 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1647
                then
                  let uu____1648 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1649 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1648
                    uu____1649
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_1653 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_1653.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_1653.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1657 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1657
                then
                  let uu____1658 =
                    let uu____1659 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1660 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1659 uu____1660 in
                  failwith uu____1658
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1664 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1664.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1664.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1666),uu____1667) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1680 =
                  let uu____1681 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1681 in
                if uu____1680
                then
                  let uu____1682 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1682
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____1694;
                FStar_Syntax_Syntax.vars = uu____1695;_},args))
              ->
              ((let uu____1716 =
                  let uu____1717 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1717 Prims.op_Negation in
                if uu____1716
                then
                  let uu____1718 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1718
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1794)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1833) ->
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
                       | ((e2,imp),uu____1854) ->
                           let pat =
                             let uu____1866 = aux argpat e2 in
                             let uu____1867 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____1866, uu____1867) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1870 ->
                      let uu____1882 =
                        let uu____1883 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____1884 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1883 uu____1884 in
                      failwith uu____1882 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____1892;
                     FStar_Syntax_Syntax.vars = uu____1893;_},uu____1894);
                FStar_Syntax_Syntax.pos = uu____1895;
                FStar_Syntax_Syntax.vars = uu____1896;_},args))
              ->
              ((let uu____1919 =
                  let uu____1920 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1920 Prims.op_Negation in
                if uu____1919
                then
                  let uu____1921 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1921
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1997)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2036) ->
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
                       | ((e2,imp),uu____2057) ->
                           let pat =
                             let uu____2069 = aux argpat e2 in
                             let uu____2070 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2069, uu____2070) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2073 ->
                      let uu____2085 =
                        let uu____2086 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2087 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2086 uu____2087 in
                      failwith uu____2085 in
                match_args [] args argpats))
          | uu____2092 ->
              let uu____2095 =
                let uu____2096 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2097 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2098 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2096 uu____2097 uu____2098 in
              failwith uu____2095 in
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
    let pat_as_arg uu____2126 =
      match uu____2126 with
      | (p,i) ->
          let uu____2136 = decorated_pattern_as_term p in
          (match uu____2136 with
           | (vars,te) ->
               let uu____2149 =
                 let uu____2152 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2152) in
               (vars, uu____2149)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2160 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2160)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2163 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2163)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2166 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2166)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2178 =
          let uu____2186 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2186 FStar_List.unzip in
        (match uu____2178 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2243 =
               let uu____2244 =
                 let uu____2245 =
                   let uu____2253 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2253, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2245 in
               mk1 uu____2244 in
             (vars1, uu____2243))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____2278)::[] -> wp
      | uu____2287 ->
          let uu____2292 =
            let uu____2293 =
              let uu____2294 =
                FStar_List.map
                  (fun uu____2301  ->
                     match uu____2301 with
                     | (x,uu____2305) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2294 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2293 in
          failwith uu____2292 in
    let uu____2308 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2308, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2323 = destruct_comp c in
        match uu____2323 with
        | (u,uu____2328,wp) ->
            let uu____2330 =
              let uu____2335 =
                let uu____2336 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2336 in
              [uu____2335] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2330;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2349 =
          let uu____2353 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2354 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2353 uu____2354 in
        match uu____2349 with | (m,uu____2356,uu____2357) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2370 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2370
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
        let uu____2398 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2398 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2420 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2420 with
             | (a,kwp) ->
                 let uu____2437 = destruct_comp m1 in
                 let uu____2441 = destruct_comp m2 in
                 ((md, a, kwp), uu____2437, uu____2441))
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
            let uu____2496 =
              let uu____2497 =
                let uu____2502 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2502] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2497;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2496
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
      let uu___127_2548 = lc in
      let uu____2549 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___127_2548.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2549;
        FStar_Syntax_Syntax.cflags =
          (uu___127_2548.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2553  ->
             let uu____2554 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2554)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2559 =
      let uu____2560 = FStar_Syntax_Subst.compress t in
      uu____2560.FStar_Syntax_Syntax.n in
    match uu____2559 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2562 -> true
    | uu____2569 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2584 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2584
        then c
        else
          (let uu____2586 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2586
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2620 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2620] in
                       let us =
                         let uu____2623 =
                           let uu____2625 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2625] in
                         u_res :: uu____2623 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2628 =
                         let uu____2629 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2630 =
                           let uu____2631 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2632 =
                             let uu____2634 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2635 =
                               let uu____2637 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2637] in
                             uu____2634 :: uu____2635 in
                           uu____2631 :: uu____2632 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2629 uu____2630 in
                       uu____2628 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2643 = destruct_comp c1 in
              match uu____2643 with
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
        let close1 uu____2669 =
          let uu____2670 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2670 in
        let uu___128_2671 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___128_2671.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___128_2671.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___128_2671.FStar_Syntax_Syntax.cflags);
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
          let uu____2685 =
            let uu____2686 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2686 in
          if uu____2685
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2691 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2691
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2693 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____2693 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2699 =
                        let uu____2700 =
                          let uu____2701 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2702 =
                            let uu____2703 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2704 =
                              let uu____2706 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2706] in
                            uu____2703 :: uu____2704 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2701 uu____2702 in
                        uu____2700 FStar_Pervasives_Native.None
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2699) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2712 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2712
         then
           let uu____2713 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2714 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2715 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2713
             uu____2714 uu____2715
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
          fun uu____2737  ->
            match uu____2737 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2747 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2747
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____2750 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____2752 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2753 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2750 uu____2752 bstr uu____2753
                  else ());
                 (let bind_it uu____2758 =
                    let uu____2759 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2759
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____2767 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____2767
                        then
                          let uu____2768 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____2770 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____2771 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2772 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____2773 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____2768 uu____2770 uu____2771 uu____2772
                            uu____2773
                        else ());
                       (let try_simplify uu____2783 =
                          let aux uu____2792 =
                            let uu____2793 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2793
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____2808 ->
                                  let uu____2809 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____2809
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____2824 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____2824
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____2856 =
                                  let uu____2859 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____2859, reason) in
                                FStar_Util.Inl uu____2856
                            | uu____2862 -> aux () in
                          let rec maybe_close t x c =
                            let uu____2877 =
                              let uu____2878 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____2878.FStar_Syntax_Syntax.n in
                            match uu____2877 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____2881) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____2885 -> c in
                          let uu____2886 =
                            let uu____2887 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____2887 in
                          if uu____2886
                          then
                            let uu____2894 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____2894
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____2905 =
                                  let uu____2906 =
                                    let uu____2909 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____2909) in
                                  FStar_Errors.Error uu____2906 in
                                raise uu____2905))
                          else
                            (let uu____2916 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____2916
                             then subst_c2 "both total"
                             else
                               (let uu____2923 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____2923
                                then
                                  let uu____2929 =
                                    let uu____2932 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____2932, "both gtot") in
                                  FStar_Util.Inl uu____2929
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____2947 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____2949 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____2949) in
                                       if uu____2947
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___129_2957 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___129_2957.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___129_2957.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____2958 =
                                           let uu____2961 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____2961, "c1 Tot") in
                                         FStar_Util.Inl uu____2958
                                       else aux ()
                                   | uu____2965 -> aux ()))) in
                        let uu____2970 = try_simplify () in
                        match uu____2970 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____2984 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____2984
                              then
                                let uu____2985 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____2986 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____2987 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____2985 uu____2986 uu____2987
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____2993 = lift_and_destruct env c1 c2 in
                            (match uu____2993 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3027 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3027]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____3029 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3029] in
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
                                   let uu____3042 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3043 =
                                     let uu____3045 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3046 =
                                       let uu____3048 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3049 =
                                         let uu____3051 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3052 =
                                           let uu____3054 =
                                             let uu____3055 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3055 in
                                           [uu____3054] in
                                         uu____3051 :: uu____3052 in
                                       uu____3048 :: uu____3049 in
                                     uu____3045 :: uu____3046 in
                                   uu____3042 :: uu____3043 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3059 =
                                     let uu____3060 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3060
                                       wp_args in
                                   uu____3059 FStar_Pervasives_Native.None
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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
              let uu____3110 =
                let uu____3111 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3111 in
              if uu____3110
              then f
              else (let uu____3113 = reason1 () in label uu____3113 r f)
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
            let uu___130_3127 = g in
            let uu____3128 =
              let uu____3129 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3129 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3128;
              FStar_TypeChecker_Env.deferred =
                (uu___130_3127.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___130_3127.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___130_3127.FStar_TypeChecker_Env.implicits)
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
      | uu____3141 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3160 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3163 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3163
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3168 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3168
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3172 = destruct_comp c1 in
                    match uu____3172 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3183 =
                            let uu____3184 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3185 =
                              let uu____3186 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3187 =
                                let uu____3189 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3190 =
                                  let uu____3192 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3192] in
                                uu____3189 :: uu____3190 in
                              uu____3186 :: uu____3187 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3184
                              uu____3185 in
                          uu____3183 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___131_3197 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_3197.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_3197.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_3197.FStar_Syntax_Syntax.cflags);
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
            let uu____3229 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3229
            then (lc, g0)
            else
              ((let uu____3234 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3234
                then
                  let uu____3235 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3236 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3235 uu____3236
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___99_3243  ->
                          match uu___99_3243 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3245 -> [])) in
                let strengthen uu____3250 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3256 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3256 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3261 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3263 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3263) in
                           if uu____3261
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3268 =
                                 let uu____3269 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3269 in
                               FStar_Syntax_Util.comp_set_flags uu____3268
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3274 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3274
                           then
                             let uu____3275 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3276 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3275 uu____3276
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3279 = destruct_comp c2 in
                           match uu____3279 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3290 =
                                   let uu____3291 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3292 =
                                     let uu____3293 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3294 =
                                       let uu____3296 =
                                         let uu____3297 =
                                           let uu____3298 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3298 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3297 in
                                       let uu____3299 =
                                         let uu____3301 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3301] in
                                       uu____3296 :: uu____3299 in
                                     uu____3293 :: uu____3294 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3291
                                     uu____3292 in
                                 uu____3290 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3307 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3307
                                 then
                                   let uu____3308 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3308
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3311 =
                  let uu___132_3312 = lc in
                  let uu____3313 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3314 =
                    let uu____3316 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3318 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3318) in
                    if uu____3316 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3313;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___132_3312.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3314;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3311,
                  (let uu___133_3322 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3322.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3322.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3322.FStar_TypeChecker_Env.implicits)
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
        let uu____3339 =
          let uu____3342 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3343 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3342, uu____3343) in
        match uu____3339 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3350 =
                let uu____3351 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3352 =
                  let uu____3353 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3354 =
                    let uu____3356 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3356] in
                  uu____3353 :: uu____3354 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3351 uu____3352 in
              uu____3350 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3363 =
                let uu____3364 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3365 =
                  let uu____3366 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3367 =
                    let uu____3369 =
                      let uu____3370 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3370 in
                    let uu____3371 =
                      let uu____3373 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3373] in
                    uu____3369 :: uu____3371 in
                  uu____3366 :: uu____3367 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3364 uu____3365 in
              uu____3363 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3380 =
                let uu____3381 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3382 =
                  let uu____3383 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3384 =
                    let uu____3386 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3387 =
                      let uu____3389 =
                        let uu____3390 =
                          let uu____3391 =
                            let uu____3392 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3392] in
                          FStar_Syntax_Util.abs uu____3391 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3390 in
                      [uu____3389] in
                    uu____3386 :: uu____3387 in
                  uu____3383 :: uu____3384 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3381 uu____3382 in
              uu____3380 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3400 = FStar_TypeChecker_Env.get_range env in
              bind uu____3400 env FStar_Pervasives_Native.None
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
          let comp uu____3422 =
            let uu____3423 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3423
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3426 =
                 let uu____3439 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3440 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3439 uu____3440 in
               match uu____3426 with
               | ((md,uu____3442,uu____3443),(u_res_t,res_t,wp_then),
                  (uu____3447,uu____3448,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3476 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3477 =
                       let uu____3478 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3479 =
                         let uu____3480 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3481 =
                           let uu____3483 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3484 =
                             let uu____3486 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3487 =
                               let uu____3489 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3489] in
                             uu____3486 :: uu____3487 in
                           uu____3483 :: uu____3484 in
                         uu____3480 :: uu____3481 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3478 uu____3479 in
                     uu____3477 FStar_Pervasives_Native.None uu____3476 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3496 =
                     let uu____3497 = FStar_Options.split_cases () in
                     uu____3497 > (Prims.parse_int "0") in
                   if uu____3496
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3502 =
                          let uu____3503 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3504 =
                            let uu____3505 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3506 =
                              let uu____3508 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3508] in
                            uu____3505 :: uu____3506 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3503 uu____3504 in
                        uu____3502 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3513 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3513;
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
      let uu____3522 =
        let uu____3523 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3523 in
      FStar_Syntax_Syntax.fvar uu____3522 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3550  ->
                 match uu____3550 with
                 | (uu____3553,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____3558 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3560 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3560
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3579 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3580 =
                 let uu____3581 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3582 =
                   let uu____3583 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3584 =
                     let uu____3586 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3587 =
                       let uu____3589 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3590 =
                         let uu____3592 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3592] in
                       uu____3589 :: uu____3590 in
                     uu____3586 :: uu____3587 in
                   uu____3583 :: uu____3584 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3581 uu____3582 in
               uu____3580 FStar_Pervasives_Native.None uu____3579 in
             let default_case =
               let post_k =
                 let uu____3600 =
                   let uu____3604 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3604] in
                 let uu____3605 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3600 uu____3605 in
               let kwp =
                 let uu____3609 =
                   let uu____3613 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3613] in
                 let uu____3614 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3609 uu____3614 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____3618 =
                   let uu____3619 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3619] in
                 let uu____3620 =
                   let uu____3621 =
                     let uu____3624 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3624 in
                   let uu____3625 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____3621 uu____3625 in
                 FStar_Syntax_Util.abs uu____3618 uu____3620
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
                 (fun uu____3646  ->
                    fun celse  ->
                      match uu____3646 with
                      | (g,cthen) ->
                          let uu____3652 =
                            let uu____3665 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3665 celse in
                          (match uu____3652 with
                           | ((md,uu____3667,uu____3668),(uu____3669,uu____3670,wp_then),
                              (uu____3672,uu____3673,wp_else)) ->
                               let uu____3684 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3684 []))
                 lcases default_case in
             let uu____3685 =
               let uu____3686 = FStar_Options.split_cases () in
               uu____3686 > (Prims.parse_int "0") in
             if uu____3685
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3690 = destruct_comp comp1 in
                match uu____3690 with
                | (uu____3694,uu____3695,wp) ->
                    let wp1 =
                      let uu____3699 =
                        let uu____3700 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3701 =
                          let uu____3702 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3703 =
                            let uu____3705 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3705] in
                          uu____3702 :: uu____3703 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3700 uu____3701 in
                      uu____3699 FStar_Pervasives_Native.None
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
          let uu____3724 =
            ((let uu____3727 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____3727) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3729 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____3729) in
          if uu____3724
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____3736 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3739 =
            (let uu____3742 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____3742) || env.FStar_TypeChecker_Env.lax in
          if uu____3739
          then c
          else
            (let uu____3745 = FStar_Syntax_Util.is_partial_return c in
             if uu____3745
             then c
             else
               (let uu____3748 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____3748
                then
                  let uu____3750 =
                    let uu____3751 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____3751 in
                  (if uu____3750
                   then
                     let uu____3753 =
                       let uu____3754 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____3755 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____3754 uu____3755 in
                     failwith uu____3753
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____3759 =
                        let uu____3760 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____3760 in
                      if uu____3759
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___134_3764 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___134_3764.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___134_3764.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___134_3764.FStar_Syntax_Syntax.effect_args);
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
                     let uu____3774 =
                       let uu____3776 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____3776
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____3774 in
                   let eq1 =
                     let uu____3779 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____3779 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____3781 =
                     let uu____3782 =
                       let uu____3786 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____3786.FStar_Syntax_Syntax.comp in
                     uu____3782 () in
                   FStar_Syntax_Util.comp_set_flags uu____3781 flags))) in
        let uu___135_3788 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___135_3788.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___135_3788.FStar_Syntax_Syntax.res_typ);
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
          let uu____3811 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____3811 with
          | FStar_Pervasives_Native.None  ->
              let uu____3816 =
                let uu____3817 =
                  let uu____3820 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____3821 = FStar_TypeChecker_Env.get_range env in
                  (uu____3820, uu____3821) in
                FStar_Errors.Error uu____3817 in
              raise uu____3816
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
            let uu____3851 =
              let uu____3852 = FStar_Syntax_Subst.compress t2 in
              uu____3852.FStar_Syntax_Syntax.n in
            match uu____3851 with
            | FStar_Syntax_Syntax.Tm_type uu____3854 -> true
            | uu____3855 -> false in
          let uu____3856 =
            let uu____3857 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____3857.FStar_Syntax_Syntax.n in
          match uu____3856 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____3862 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____3869 =
                  let uu____3870 =
                    let uu____3871 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____3871 in
                  (FStar_Pervasives_Native.None, uu____3870) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____3869 in
              let e1 =
                let uu____3877 =
                  let uu____3878 =
                    let uu____3879 = FStar_Syntax_Syntax.as_arg e in
                    [uu____3879] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____3878 in
                uu____3877 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____3885 -> (e, lc)
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
              (let uu____3912 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____3912 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____3925 -> false) in
          let gopt =
            if use_eq
            then
              let uu____3937 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____3937, false)
            else
              (let uu____3941 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____3941, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____3947) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___136_3951 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___136_3951.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___136_3951.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___136_3951.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____3955 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____3955 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___137_3960 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___137_3960.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___137_3960.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___137_3960.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___138_3963 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___138_3963.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___138_3963.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___138_3963.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____3968 =
                     let uu____3969 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____3969
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____3973 =
                          let uu____3974 = FStar_Syntax_Subst.compress f1 in
                          uu____3974.FStar_Syntax_Syntax.n in
                        match uu____3973 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____3977,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____3979;
                                          FStar_Syntax_Syntax.vars =
                                            uu____3980;_},uu____3981)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___139_3993 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___139_3993.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___139_3993.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___139_3993.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____3994 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____3998 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____3998
                              then
                                let uu____3999 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4000 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4001 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4002 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____3999 uu____4000 uu____4001 uu____4002
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4005 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____4005 with
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
                                  let uu____4015 = destruct_comp ct in
                                  (match uu____4015 with
                                   | (u_t,uu____4021,uu____4022) ->
                                       let wp =
                                         let uu____4025 =
                                           let uu____4026 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4027 =
                                             let uu____4028 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4029 =
                                               let uu____4031 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4031] in
                                             uu____4028 :: uu____4029 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4026 uu____4027 in
                                         uu____4025
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4037 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4037 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4043 =
                                             let uu____4044 =
                                               let uu____4045 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4045] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4044 in
                                           uu____4043
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4051 =
                                         let uu____4054 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4065 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4066 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4054
                                           uu____4065 e cret uu____4066 in
                                       (match uu____4051 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___140_4071 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___140_4071.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___140_4071.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4073 =
                                                let uu____4074 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4074 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____4073
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4081 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4081
                                              then
                                                let uu____4082 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4082
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___100_4089  ->
                             match uu___100_4089 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4091 -> [])) in
                   let lc1 =
                     let uu___141_4093 = lc in
                     let uu____4094 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4094;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___142_4096 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___142_4096.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___142_4096.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___142_4096.FStar_TypeChecker_Env.implicits)
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
        let uu____4117 =
          let uu____4118 =
            let uu____4119 =
              let uu____4120 =
                let uu____4121 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4121 in
              [uu____4120] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4119 in
          uu____4118 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4117 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4130 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4130
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4140 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4148 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4164)::(ens,uu____4166)::uu____4167 ->
                    let uu____4182 =
                      let uu____4184 = norm req in
                      FStar_Pervasives_Native.Some uu____4184 in
                    let uu____4185 =
                      let uu____4186 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4186 in
                    (uu____4182, uu____4185)
                | uu____4188 ->
                    let uu____4193 =
                      let uu____4194 =
                        let uu____4197 =
                          let uu____4198 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4198 in
                        (uu____4197, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4194 in
                    raise uu____4193)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4208)::uu____4209 ->
                    let uu____4219 =
                      let uu____4222 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____4222 in
                    (match uu____4219 with
                     | (us_r,uu____4239) ->
                         let uu____4240 =
                           let uu____4243 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____4243 in
                         (match uu____4240 with
                          | (us_e,uu____4260) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4263 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4263
                                  us_r in
                              let as_ens =
                                let uu____4265 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4265
                                  us_e in
                              let req =
                                let uu____4268 =
                                  let uu____4269 =
                                    let uu____4270 =
                                      let uu____4276 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4276] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4270 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4269 in
                                uu____4268 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4289 =
                                  let uu____4290 =
                                    let uu____4291 =
                                      let uu____4297 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4297] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4291 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4290 in
                                uu____4289 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4308 =
                                let uu____4310 = norm req in
                                FStar_Pervasives_Native.Some uu____4310 in
                              let uu____4311 =
                                let uu____4312 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4312 in
                              (uu____4308, uu____4311)))
                | uu____4314 -> failwith "Impossible"))
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
      (let uu____4334 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4334
       then
         let uu____4335 = FStar_Syntax_Print.term_to_string tm in
         let uu____4336 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4335 uu____4336
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
        (let uu____4358 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4358
         then
           let uu____4359 = FStar_Syntax_Print.term_to_string tm in
           let uu____4360 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4359
             uu____4360
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4366 =
      let uu____4367 =
        let uu____4368 = FStar_Syntax_Subst.compress t in
        uu____4368.FStar_Syntax_Syntax.n in
      match uu____4367 with
      | FStar_Syntax_Syntax.Tm_app uu____4370 -> false
      | uu____4378 -> true in
    if uu____4366
    then t
    else
      (let uu____4380 = FStar_Syntax_Util.head_and_args t in
       match uu____4380 with
       | (head1,args) ->
           let uu____4400 =
             let uu____4401 =
               let uu____4402 = FStar_Syntax_Subst.compress head1 in
               uu____4402.FStar_Syntax_Syntax.n in
             match uu____4401 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4404 -> false in
           if uu____4400
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____4416 ->
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
             let uu____4446 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4446 with
             | (formals,uu____4454) ->
                 let n_implicits =
                   let uu____4464 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4504  ->
                             match uu____4504 with
                             | (uu____4508,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____4464 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4583 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4583 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4604 =
                     let uu____4605 =
                       let uu____4608 =
                         let uu____4609 = FStar_Util.string_of_int n_expected in
                         let uu____4616 = FStar_Syntax_Print.term_to_string e in
                         let uu____4617 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4609 uu____4616 uu____4617 in
                       let uu____4624 = FStar_TypeChecker_Env.get_range env in
                       (uu____4608, uu____4624) in
                     FStar_Errors.Error uu____4605 in
                   raise uu____4604
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___101_4642 =
             match uu___101_4642 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4659 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4659 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____4720) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4742,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____4761 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____4761 with
                           | (v1,uu____4782,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____4792 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____4792 with
                                | (args,bs3,subst3,g') ->
                                    let uu____4841 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____4841)))
                      | (uu____4855,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____4879 =
                      let uu____4893 = inst_n_binders t in
                      aux [] uu____4893 bs1 in
                    (match uu____4879 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____4931) -> (e, torig, guard)
                          | (uu____4947,[]) when
                              let uu____4963 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____4963 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____4964 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____4981 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____4992 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____4999 =
      let uu____5001 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5001
        (FStar_List.map
           (fun u  ->
              let uu____5008 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5008 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____4999 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5022 = FStar_Util.set_is_empty x in
      if uu____5022
      then []
      else
        (let s =
           let uu____5027 =
             let uu____5029 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5029 in
           FStar_All.pipe_right uu____5027 FStar_Util.set_elements in
         (let uu____5034 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5034
          then
            let uu____5035 =
              let uu____5036 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5036 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5035
          else ());
         (let r =
            let uu____5041 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____5041 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5053 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5053
                     then
                       let uu____5054 =
                         let uu____5055 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5055 in
                       let uu____5056 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5057 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5054 uu____5056 uu____5057
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
        let uu____5076 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5076 FStar_Util.fifo_set_elements in
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
        | ([],uu____5103) -> generalized_univ_names
        | (uu____5107,[]) -> explicit_univ_names
        | uu____5111 ->
            let uu____5116 =
              let uu____5117 =
                let uu____5120 =
                  let uu____5121 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5121 in
                (uu____5120, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5117 in
            raise uu____5116
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term)
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
      (let uu____5137 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5137
       then
         let uu____5138 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5138
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5143 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5143
        then
          let uu____5144 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5144
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
      let uu____5177 =
        let uu____5178 =
          FStar_Util.for_all
            (fun uu____5185  ->
               match uu____5185 with
               | (uu____5189,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5178 in
      if uu____5177
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____5210 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5210
            then
              let uu____5211 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5211
            else ());
           (let c1 =
              let uu____5214 = FStar_TypeChecker_Env.should_verify env in
              if uu____5214
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
            (let uu____5217 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5217
             then
               let uu____5218 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5218
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5252 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5252 FStar_Util.set_elements in
         let uu____5296 =
           let uu____5314 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5380  ->
                     match uu____5380 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____5415 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____5415
                           then
                             let uu____5416 =
                               let uu____5417 =
                                 let uu____5419 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____5419
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____5417
                                 (FStar_String.concat ", ") in
                             let uu____5434 =
                               let uu____5435 =
                                 let uu____5437 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____5437
                                   (FStar_List.map
                                      (fun uu____5454  ->
                                         match uu____5454 with
                                         | (u,t2) ->
                                             let uu____5459 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____5460 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____5459 uu____5460)) in
                               FStar_All.pipe_right uu____5435
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____5416 uu____5434
                           else ());
                          (let univs2 =
                             let uu____5465 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____5480  ->
                                    match uu____5480 with
                                    | (uu____5485,t2) ->
                                        let uu____5487 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____5487) univs1 uu____5465 in
                           let uvs = gen_uvars uvt in
                           (let uu____5500 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____5500
                            then
                              let uu____5501 =
                                let uu____5502 =
                                  let uu____5504 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____5504
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____5502
                                  (FStar_String.concat ", ") in
                              let uu____5519 =
                                let uu____5520 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____5539  ->
                                          match uu____5539 with
                                          | (u,t2) ->
                                              let uu____5544 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____5545 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____5544 uu____5545)) in
                                FStar_All.pipe_right uu____5520
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____5501 uu____5519
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____5314 FStar_List.unzip in
         match uu____5296 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5656 = FStar_List.hd univs1 in
               let uu____5659 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____5672 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____5672
                      then out
                      else
                        (let uu____5675 =
                           let uu____5676 =
                             let uu____5679 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____5679) in
                           FStar_Errors.Error uu____5676 in
                         raise uu____5675)) uu____5656 uu____5659 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5684 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5684
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
                      (fun uu____5731  ->
                         match uu____5731 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5775  ->
                                       match uu____5775 with
                                       | (u,k) ->
                                           let uu____5783 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____5783 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5789;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5790;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____5794,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____5796;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____5797;_},uu____5798);
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5799;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5800;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____5814 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5818 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____5821 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____5821 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____5842 =
                                                         let uu____5844 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____5844 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5842 kres in
                                                     let t =
                                                       let uu____5847 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5847
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____5850 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____5868 ->
                                   let uu____5876 = (e, c) in
                                   (match uu____5876 with
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
                                          let uu____5887 =
                                            let uu____5888 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____5888.FStar_Syntax_Syntax.n in
                                          match uu____5887 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5901 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____5901 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____5910 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____5912 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____5912)) in
                             (match uu____5850 with
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
      (let uu____5952 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____5952
       then
         let uu____5953 =
           let uu____5954 =
             FStar_List.map
               (fun uu____5963  ->
                  match uu____5963 with
                  | (lb,uu____5968,uu____5969) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____5954 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____5953
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5983  ->
              match uu____5983 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____5998 =
           let uu____6005 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6025  ->
                     match uu____6025 with | (uu____6031,e,c) -> (e, c))) in
           gen env uu____6005 in
         match uu____5998 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6067  ->
                     match uu____6067 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____6116  ->
                  fun uu____6117  ->
                    match (uu____6116, uu____6117) with
                    | ((l,uu____6144,uu____6145),(us,e,c)) ->
                        ((let uu____6165 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6165
                          then
                            let uu____6166 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6167 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6168 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6169 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6166 uu____6167 uu____6168 uu____6169
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6193  ->
              match uu____6193 with
              | (l,generalized_univs,t,c) ->
                  let uu____6211 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6211, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6248 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6248 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____6252 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____6252) in
          let is_var e1 =
            let uu____6258 =
              let uu____6259 = FStar_Syntax_Subst.compress e1 in
              uu____6259.FStar_Syntax_Syntax.n in
            match uu____6258 with
            | FStar_Syntax_Syntax.Tm_name uu____6261 -> true
            | uu____6262 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___143_6279 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___143_6279.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___143_6279.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____6280 -> e2 in
          let env2 =
            let uu___144_6282 = env1 in
            let uu____6283 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___144_6282.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___144_6282.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___144_6282.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___144_6282.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___144_6282.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___144_6282.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___144_6282.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___144_6282.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___144_6282.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___144_6282.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___144_6282.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___144_6282.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___144_6282.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___144_6282.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___144_6282.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6283;
              FStar_TypeChecker_Env.is_iface =
                (uu___144_6282.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___144_6282.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___144_6282.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___144_6282.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___144_6282.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___144_6282.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___144_6282.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___144_6282.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___144_6282.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___144_6282.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___144_6282.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6284 = check env2 t1 t2 in
          match uu____6284 with
          | FStar_Pervasives_Native.None  ->
              let uu____6288 =
                let uu____6289 =
                  let uu____6292 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6293 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6292, uu____6293) in
                FStar_Errors.Error uu____6289 in
              raise uu____6288
          | FStar_Pervasives_Native.Some g ->
              ((let uu____6298 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6298
                then
                  let uu____6299 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6299
                else ());
               (let uu____6301 = decorate e t2 in (uu____6301, g)))
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
        let uu____6326 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6326
        then
          let uu____6329 = discharge g1 in
          let uu____6330 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6329, uu____6330)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6339 =
               let uu____6340 =
                 let uu____6341 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6341 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6340
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6339
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6343 = destruct_comp c1 in
           match uu____6343 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6354 = FStar_TypeChecker_Env.get_range env in
                 let uu____6355 =
                   let uu____6356 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6357 =
                     let uu____6358 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6359 =
                       let uu____6361 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6361] in
                     uu____6358 :: uu____6359 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6356 uu____6357 in
                 uu____6355 FStar_Pervasives_Native.None uu____6354 in
               ((let uu____6367 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6367
                 then
                   let uu____6368 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6368
                 else ());
                (let g2 =
                   let uu____6371 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6371 in
                 let uu____6372 = discharge g2 in
                 let uu____6373 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6372, uu____6373))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6397 =
        match uu___102_6397 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6402)::[] -> f fst1
        | uu____6411 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6416 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6416
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6423 =
          let uu____6425 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6425 in
        FStar_All.pipe_right uu____6423
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6435 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6435
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___103_6446 =
        match uu___103_6446 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6451)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6462)::[] ->
            let uu____6477 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6477
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6480 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6487 =
          let uu____6492 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____6492) in
        let uu____6497 =
          let uu____6503 =
            let uu____6508 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____6508) in
          let uu____6513 =
            let uu____6519 =
              let uu____6524 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____6524) in
            let uu____6529 =
              let uu____6535 =
                let uu____6540 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____6540) in
              let uu____6545 =
                let uu____6551 =
                  let uu____6556 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____6556) in
                [uu____6551; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____6535 :: uu____6545 in
            uu____6519 :: uu____6529 in
          uu____6503 :: uu____6513 in
        uu____6487 :: uu____6497 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6593 =
            FStar_Util.find_map table
              (fun uu____6603  ->
                 match uu____6603 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____6616 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____6616
                     else FStar_Pervasives_Native.None) in
          (match uu____6593 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____6619 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6624 =
      let uu____6625 = FStar_Syntax_Util.un_uinst l in
      uu____6625.FStar_Syntax_Syntax.n in
    match uu____6624 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____6628 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6648)::uu____6649 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6655 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6659,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____6660))::uu____6661 -> bs
      | uu____6670 ->
          let uu____6671 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6671 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____6674 =
                 let uu____6675 = FStar_Syntax_Subst.compress t in
                 uu____6675.FStar_Syntax_Syntax.n in
               (match uu____6674 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6678) ->
                    let uu____6687 =
                      FStar_Util.prefix_until
                        (fun uu___104_6709  ->
                           match uu___104_6709 with
                           | (uu____6713,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6714)) ->
                               false
                           | uu____6716 -> true) bs' in
                    (match uu____6687 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____6734,uu____6735) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____6772,uu____6773) ->
                         let uu____6810 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6821  ->
                                   match uu____6821 with
                                   | (x,uu____6826) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____6810
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____6853  ->
                                     match uu____6853 with
                                     | (x,i) ->
                                         let uu____6864 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____6864, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____6870 -> bs))
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
          let uu____6914 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____6914
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____6940 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____6940
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____6942 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____6942))
         else ());
        (let fv =
           let uu____6945 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____6945
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
         let uu____6951 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___145_6958 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___145_6958.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___145_6958.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___145_6958.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___145_6958.FStar_Syntax_Syntax.sigattrs)
           }), uu____6951))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_6970 =
        match uu___105_6970 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____6971 -> false in
      let reducibility uu___106_6975 =
        match uu___106_6975 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____6976 -> false in
      let assumption uu___107_6980 =
        match uu___107_6980 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____6981 -> false in
      let reification uu___108_6985 =
        match uu___108_6985 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____6986 -> true
        | uu____6987 -> false in
      let inferred uu___109_6991 =
        match uu___109_6991 with
        | FStar_Syntax_Syntax.Discriminator uu____6992 -> true
        | FStar_Syntax_Syntax.Projector uu____6993 -> true
        | FStar_Syntax_Syntax.RecordType uu____6996 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7001 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7006 -> false in
      let has_eq uu___110_7010 =
        match uu___110_7010 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7011 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7057 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7061 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7064 =
        let uu____7065 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7068  ->
                  match uu___111_7068 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7069 -> false)) in
        FStar_All.pipe_right uu____7065 Prims.op_Negation in
      if uu____7064
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7081 =
            let uu____7082 =
              let uu____7085 =
                let uu____7086 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7086 msg in
              (uu____7085, r) in
            FStar_Errors.Error uu____7082 in
          raise uu____7081 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7094 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7106 =
            let uu____7107 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7107 in
          if uu____7106 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____7111),uu____7112) ->
              ((let uu____7121 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7121
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7124 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7124
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7129 ->
              let uu____7134 =
                let uu____7135 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7135 in
              if uu____7134 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7140 ->
              let uu____7144 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7144 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7147 ->
              let uu____7151 =
                let uu____7152 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7152 in
              if uu____7151 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7157 ->
              let uu____7158 =
                let uu____7159 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7159 in
              if uu____7158 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7164 ->
              let uu____7165 =
                let uu____7166 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7166 in
              if uu____7165 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7171 ->
              let uu____7178 =
                let uu____7179 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7179 in
              if uu____7178 then err'1 () else ()
          | uu____7184 -> ()))
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
                          let uu____7249 =
                            let uu____7251 =
                              let uu____7252 =
                                let uu____7256 =
                                  let uu____7257 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7257 in
                                (uu____7256, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7252 in
                            FStar_Syntax_Syntax.mk uu____7251 in
                          uu____7249 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7285  ->
                                  match uu____7285 with
                                  | (x,imp) ->
                                      let uu____7292 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7292, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7296 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7296 in
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
                             let uu____7304 =
                               let uu____7305 =
                                 let uu____7306 =
                                   let uu____7307 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7308 =
                                     let uu____7309 =
                                       let uu____7310 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7310 in
                                     [uu____7309] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7307
                                     uu____7308 in
                                 uu____7306 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7305 in
                             FStar_Syntax_Util.refine x uu____7304 in
                           let uu____7315 =
                             let uu___146_7316 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___146_7316.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___146_7316.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7315) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7327 =
                          FStar_List.map
                            (fun uu____7340  ->
                               match uu____7340 with
                               | (x,uu____7347) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7327 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7374  ->
                                match uu____7374 with
                                | (x,uu____7381) ->
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
                             (let uu____7392 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____7392)
                               ||
                               (let uu____7394 =
                                  let uu____7395 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7395.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7394) in
                           let quals =
                             let uu____7398 =
                               let uu____7400 =
                                 let uu____7402 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7402
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7405 =
                                 FStar_List.filter
                                   (fun uu___112_7408  ->
                                      match uu___112_7408 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7409 -> false) iquals in
                               FStar_List.append uu____7400 uu____7405 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7398 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7422 =
                                 let uu____7423 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7423 in
                               FStar_Syntax_Syntax.mk_Total uu____7422 in
                             let uu____7424 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7424 in
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
                           (let uu____7427 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7427
                            then
                              let uu____7428 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7428
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
                                             fun uu____7461  ->
                                               match uu____7461 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7477 =
                                                       let uu____7479 =
                                                         let uu____7480 =
                                                           let uu____7484 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7484,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7480 in
                                                       pos uu____7479 in
                                                     (uu____7477, b)
                                                   else
                                                     (let uu____7487 =
                                                        let uu____7489 =
                                                          let uu____7490 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7490 in
                                                        pos uu____7489 in
                                                      (uu____7487, b)))) in
                                   let pat_true =
                                     let uu____7500 =
                                       let uu____7502 =
                                         let uu____7503 =
                                           let uu____7510 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____7510, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7503 in
                                       pos uu____7502 in
                                     (uu____7500,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____7528 =
                                       let uu____7530 =
                                         let uu____7531 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7531 in
                                       pos uu____7530 in
                                     (uu____7528,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____7538 =
                                     let uu____7540 =
                                       let uu____7541 =
                                         let uu____7553 =
                                           let uu____7555 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7556 =
                                             let uu____7558 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7558] in
                                           uu____7555 :: uu____7556 in
                                         (arg_exp, uu____7553) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7541 in
                                     FStar_Syntax_Syntax.mk uu____7540 in
                                   uu____7538 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____7567 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7567
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
                                let uu____7574 =
                                  let uu____7577 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____7577 in
                                let uu____7578 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7574;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7578
                                } in
                              let impl =
                                let uu____7581 =
                                  let uu____7582 =
                                    let uu____7586 =
                                      let uu____7588 =
                                        let uu____7589 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7589
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7588] in
                                    ((false, [lb]), uu____7586) in
                                  FStar_Syntax_Syntax.Sig_let uu____7582 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7581;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____7600 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7600
                               then
                                 let uu____7601 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7601
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
                                fun uu____7630  ->
                                  match uu____7630 with
                                  | (a,uu____7634) ->
                                      let uu____7635 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7635 with
                                       | (field_name,uu____7639) ->
                                           let field_proj_tm =
                                             let uu____7641 =
                                               let uu____7642 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7642 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7641 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7654 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7678  ->
                                    match uu____7678 with
                                    | (x,uu____7683) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7685 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7685 with
                                         | (field_name,uu____7690) ->
                                             let t =
                                               let uu____7692 =
                                                 let uu____7693 =
                                                   let uu____7695 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7695 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7693 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7692 in
                                             let only_decl =
                                               (let uu____7699 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____7699)
                                                 ||
                                                 (let uu____7701 =
                                                    let uu____7702 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7702.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7701) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7712 =
                                                   FStar_List.filter
                                                     (fun uu___113_7715  ->
                                                        match uu___113_7715
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7716 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7712
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_7725  ->
                                                         match uu___114_7725
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7726 ->
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
                                             ((let uu____7729 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7729
                                               then
                                                 let uu____7730 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7730
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
                                                           fun uu____7760  ->
                                                             match uu____7760
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7776
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____7776,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7787
                                                                    =
                                                                    let uu____7789
                                                                    =
                                                                    let uu____7790
                                                                    =
                                                                    let uu____7794
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____7794,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7790 in
                                                                    pos
                                                                    uu____7789 in
                                                                    (uu____7787,
                                                                    b))
                                                                   else
                                                                    (let uu____7797
                                                                    =
                                                                    let uu____7799
                                                                    =
                                                                    let uu____7800
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7800 in
                                                                    pos
                                                                    uu____7799 in
                                                                    (uu____7797,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____7809 =
                                                     let uu____7811 =
                                                       let uu____7812 =
                                                         let uu____7819 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____7819,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7812 in
                                                     pos uu____7811 in
                                                   let uu____7824 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____7809,
                                                     FStar_Pervasives_Native.None,
                                                     uu____7824) in
                                                 let body =
                                                   let uu____7831 =
                                                     let uu____7833 =
                                                       let uu____7834 =
                                                         let uu____7846 =
                                                           let uu____7848 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____7848] in
                                                         (arg_exp,
                                                           uu____7846) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7834 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7833 in
                                                   uu____7831
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____7858 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____7858
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
                                                   let uu____7864 =
                                                     let uu____7867 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____7867 in
                                                   let uu____7868 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7864;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7868
                                                   } in
                                                 let impl =
                                                   let uu____7871 =
                                                     let uu____7872 =
                                                       let uu____7876 =
                                                         let uu____7878 =
                                                           let uu____7879 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____7879
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____7878] in
                                                       ((false, [lb]),
                                                         uu____7876) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____7872 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____7871;
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
                                                 (let uu____7890 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____7890
                                                  then
                                                    let uu____7891 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7891
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7654 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____7925) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____7928 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____7928 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____7941 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____7941 with
                    | (formals,uu____7950) ->
                        let uu____7959 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____7981 =
                                   let uu____7982 =
                                     let uu____7983 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____7983 in
                                   FStar_Ident.lid_equals typ_lid uu____7982 in
                                 if uu____7981
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____7993,uvs',tps,typ0,uu____7997,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8014 -> failwith "Impossible"
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
                        (match uu____7959 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8055 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8055 with
                              | (indices,uu____8064) ->
                                  let refine_domain =
                                    let uu____8074 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8078  ->
                                              match uu___115_8078 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8079 -> true
                                              | uu____8084 -> false)) in
                                    if uu____8074
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8091 =
                                      match uu___116_8091 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8093,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8100 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8101 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8101 with
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
                                    let uu____8109 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8109 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8147  ->
                                               fun uu____8148  ->
                                                 match (uu____8147,
                                                         uu____8148)
                                                 with
                                                 | ((x,uu____8158),(x',uu____8160))
                                                     ->
                                                     let uu____8165 =
                                                       let uu____8169 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8169) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8165) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8170 -> []