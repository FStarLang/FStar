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
    | FStar_Syntax_Syntax.Tm_type uu____24 -> true
    | uu____25 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____33 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____33
      (FStar_List.filter
         (fun uu____42  ->
            match uu____42 with
            | (x,uu____46) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____58 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____60 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____60) in
        if uu____58
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____62 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____62 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____71 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____71
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___99_77  ->
    match uu___99_77 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____79);
        FStar_Syntax_Syntax.tk = uu____80;
        FStar_Syntax_Syntax.pos = uu____81;
        FStar_Syntax_Syntax.vars = uu____82;_} -> uv
    | uu____101 -> failwith "Impossible"
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
          let uu____124 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____124 with
          | FStar_Pervasives_Native.Some (uu____137::(tm,uu____139)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____179 ->
              let uu____186 = new_uvar_aux env k in
              (match uu____186 with
               | (t,u) ->
                   let g =
                     let uu___119_198 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____199 =
                       let uu____207 =
                         let uu____214 = as_uvar u in
                         (reason, env, uu____214, t, k, r) in
                       [uu____207] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_198.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_198.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_198.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____199
                     } in
                   let uu____227 =
                     let uu____231 =
                       let uu____234 = as_uvar u in (uu____234, r) in
                     [uu____231] in
                   (t, uu____227, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____254 =
        let uu____255 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____255 in
      if uu____254
      then
        let us =
          let uu____259 =
            let uu____261 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____272  ->
                 match uu____272 with
                 | (x,uu____276) -> FStar_Syntax_Print.uvar_to_string x)
              uu____261 in
          FStar_All.pipe_right uu____259 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____282 =
            let uu____283 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____283 in
          FStar_Errors.err r uu____282);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____295  ->
      match uu____295 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____302;
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
                   let uu____334 =
                     let uu____335 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____335.FStar_Syntax_Syntax.n in
                   match uu____334 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____340 = FStar_Syntax_Util.type_u () in
                       (match uu____340 with
                        | (k,uu____346) ->
                            let t2 =
                              let uu____348 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____348
                                FStar_Pervasives_Native.fst in
                            ((let uu___120_354 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_354.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_354.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____355 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____380) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____387) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____433) ->
                       let uu____446 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____483  ->
                                 fun uu____484  ->
                                   match (uu____483, uu____484) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____526 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____526 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____446 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____587 = aux must_check_ty1 scope body in
                            (match uu____587 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____604 =
                                         FStar_Options.ml_ish () in
                                       if uu____604
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____611 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____611
                                   then
                                     let uu____612 =
                                       FStar_Range.string_of_range r in
                                     let uu____613 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____614 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____612 uu____613 uu____614
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____622 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____630 =
                            let uu____633 =
                              let uu____634 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____634
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____633 in
                          (uu____630, false)) in
                 let uu____641 =
                   let uu____646 = t_binders env in aux false uu____646 e in
                 match uu____641 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____663 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____663
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____667 =
                                let uu____668 =
                                  let uu____671 =
                                    let uu____672 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____672 in
                                  (uu____671, rng) in
                                FStar_Errors.Error uu____668 in
                              raise uu____667)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____679 ->
               let uu____680 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____680 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____751) ->
              let uu____756 = FStar_Syntax_Util.type_u () in
              (match uu____756 with
               | (k,uu____769) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_772 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_772.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_772.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____773 =
                     let uu____776 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____776 t in
                   (match uu____773 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_790 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___122_790.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____796 = FStar_Syntax_Util.type_u () in
              (match uu____796 with
               | (t,uu____809) ->
                   let x1 =
                     let uu___123_811 = x in
                     let uu____812 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_811.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_811.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____812
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
              let uu____830 = FStar_Syntax_Util.type_u () in
              (match uu____830 with
               | (t,uu____843) ->
                   let x1 =
                     let uu___124_845 = x in
                     let uu____846 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_845.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_845.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____846
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____872 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____945  ->
                        fun uu____946  ->
                          match (uu____945, uu____946) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1045 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1045 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____872 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1153 =
                       let uu____1156 =
                         let uu____1157 =
                           let uu____1162 =
                             let uu____1165 =
                               let uu____1166 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1167 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1166
                                 uu____1167 in
                             uu____1165 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1162,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1157 in
                       FStar_Syntax_Syntax.mk uu____1156 in
                     uu____1153 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1184 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1190 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1196 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1184, uu____1190, uu____1196, env2, e,
                     (let uu___125_1209 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___125_1209.FStar_Syntax_Syntax.p)
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
                  (fun uu____1264  ->
                     match uu____1264 with
                     | (p2,imp) ->
                         let uu____1275 = elaborate_pat env1 p2 in
                         (uu____1275, imp)) pats in
              let uu____1278 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1278 with
               | (uu____1282,t) ->
                   let uu____1284 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1284 with
                    | (f,uu____1294) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1361::uu____1362) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1388::uu____1389,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1432  ->
                                      match uu____1432 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1448 =
                                                   let uu____1450 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____1450 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1448
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1452 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1452, true)
                                           | uu____1455 ->
                                               let uu____1457 =
                                                 let uu____1458 =
                                                   let uu____1461 =
                                                     let uu____1462 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1462 in
                                                   (uu____1461,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1458 in
                                               raise uu____1457)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1502,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____1503))
                                   when p_imp ->
                                   let uu____1505 = aux formals' pats' in
                                   (p2, true) :: uu____1505
                               | (uu____1514,FStar_Pervasives_Native.Some
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
                                   let uu____1520 = aux formals' pats2 in
                                   (p3, true) :: uu____1520
                               | (uu____1529,imp) ->
                                   let uu____1533 =
                                     let uu____1537 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1537) in
                                   let uu____1539 = aux formals' pats' in
                                   uu____1533 :: uu____1539) in
                        let uu___126_1547 = p1 in
                        let uu____1549 =
                          let uu____1550 =
                            let uu____1557 = aux f pats1 in (fv, uu____1557) in
                          FStar_Syntax_Syntax.Pat_cons uu____1550 in
                        {
                          FStar_Syntax_Syntax.v = uu____1549;
                          FStar_Syntax_Syntax.p =
                            (uu___126_1547.FStar_Syntax_Syntax.p)
                        }))
          | uu____1566 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1589 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1589 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1619 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1619 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____1632 =
                     let uu____1633 =
                       let uu____1636 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1636, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1633 in
                   raise uu____1632
               | uu____1645 -> (b, a, w, arg, p3)) in
        let uu____1650 = one_pat true env p in
        match uu____1650 with
        | (b,uu____1664,uu____1665,tm,p1) -> (b, tm, p1)
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
          | (uu____1703,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1705)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1710,FStar_Syntax_Syntax.Tm_constant uu____1711) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1715 =
                    let uu____1716 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1717 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1716 uu____1717 in
                  failwith uu____1715)
               else ();
               (let uu____1720 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1720
                then
                  let uu____1721 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1722 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1721
                    uu____1722
                else ());
               pkg p1.FStar_Syntax_Syntax.v)
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1727 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1727
                then
                  let uu____1728 =
                    let uu____1729 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1730 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1729 uu____1730 in
                  failwith uu____1728
                else ());
               pkg p1.FStar_Syntax_Syntax.v)
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1733),uu____1734) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1749 =
                  let uu____1750 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1750 in
                if uu____1749
                then
                  let uu____1751 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1751
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1763;
                FStar_Syntax_Syntax.pos = uu____1764;
                FStar_Syntax_Syntax.vars = uu____1765;_},args))
              ->
              ((let uu____1790 =
                  let uu____1791 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1791 Prims.op_Negation in
                if uu____1790
                then
                  let uu____1792 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1792
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1873)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1917) ->
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
                       | ((e2,imp),uu____1943) ->
                           let pat =
                             let uu____1958 = aux argpat e2 in
                             let uu____1959 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____1958, uu____1959) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1962 ->
                      let uu____1975 =
                        let uu____1976 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____1977 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1976 uu____1977 in
                      failwith uu____1975 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____1985;
                     FStar_Syntax_Syntax.pos = uu____1986;
                     FStar_Syntax_Syntax.vars = uu____1987;_},uu____1988);
                FStar_Syntax_Syntax.tk = uu____1989;
                FStar_Syntax_Syntax.pos = uu____1990;
                FStar_Syntax_Syntax.vars = uu____1991;_},args))
              ->
              ((let uu____2020 =
                  let uu____2021 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2021 Prims.op_Negation in
                if uu____2020
                then
                  let uu____2022 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2022
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2103)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2147) ->
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
                       | ((e2,imp),uu____2173) ->
                           let pat =
                             let uu____2188 = aux argpat e2 in
                             let uu____2189 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2188, uu____2189) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2192 ->
                      let uu____2205 =
                        let uu____2206 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2207 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2206 uu____2207 in
                      failwith uu____2205 in
                match_args [] args argpats))
          | uu____2212 ->
              let uu____2215 =
                let uu____2216 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2217 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2218 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2216 uu____2217 uu____2218 in
              failwith uu____2215 in
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
    let pat_as_arg uu____2247 =
      match uu____2247 with
      | (p,i) ->
          let uu____2257 = decorated_pattern_as_term p in
          (match uu____2257 with
           | (vars,te) ->
               let uu____2270 =
                 let uu____2273 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2273) in
               (vars, uu____2270)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2281 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2281)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2284 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2284)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2287 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2287)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2299 =
          let uu____2307 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2307 FStar_List.unzip in
        (match uu____2299 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2364 =
               let uu____2365 =
                 let uu____2366 =
                   let uu____2376 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2376, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2366 in
               mk1 uu____2365 in
             (vars1, uu____2364))
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
      | (wp,uu____2406)::[] -> wp
      | uu____2419 ->
          let uu____2425 =
            let uu____2426 =
              let uu____2427 =
                FStar_List.map
                  (fun uu____2434  ->
                     match uu____2434 with
                     | (x,uu____2438) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2427 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2426 in
          failwith uu____2425 in
    let uu____2442 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2442, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2459 = destruct_comp c in
        match uu____2459 with
        | (u,uu____2464,wp) ->
            let uu____2466 =
              let uu____2472 =
                let uu____2473 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2473 in
              [uu____2472] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2466;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2486 =
          let uu____2490 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2491 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2490 uu____2491 in
        match uu____2486 with | (m,uu____2493,uu____2494) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2507 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2507
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
        let uu____2535 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2535 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2557 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2557 with
             | (a,kwp) ->
                 let uu____2574 = destruct_comp m1 in
                 let uu____2578 = destruct_comp m2 in
                 ((md, a, kwp), uu____2574, uu____2578))
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
            let uu____2635 =
              let uu____2636 =
                let uu____2642 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2642] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2636;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2635
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
      let uu___127_2689 = lc in
      let uu____2690 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___127_2689.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2690;
        FStar_Syntax_Syntax.cflags =
          (uu___127_2689.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2695  ->
             let uu____2696 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2696)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2701 =
      let uu____2702 = FStar_Syntax_Subst.compress t in
      uu____2702.FStar_Syntax_Syntax.n in
    match uu____2701 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2705 -> true
    | uu____2713 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2728 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2728
        then c
        else
          (let uu____2730 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2730
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2766 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2766] in
                       let us =
                         let uu____2769 =
                           let uu____2771 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2771] in
                         u_res :: uu____2769 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2775 =
                         let uu____2776 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2777 =
                           let uu____2778 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2779 =
                             let uu____2781 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2782 =
                               let uu____2784 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2784] in
                             uu____2781 :: uu____2782 in
                           uu____2778 :: uu____2779 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2776 uu____2777 in
                       uu____2775 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2790 = destruct_comp c1 in
              match uu____2790 with
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
        let close1 uu____2816 =
          let uu____2817 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2817 in
        let uu___128_2818 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___128_2818.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___128_2818.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___128_2818.FStar_Syntax_Syntax.cflags);
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
          let uu____2832 =
            let uu____2833 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2833 in
          if uu____2832
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2838 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2838
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2840 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____2840 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2846 =
                        let uu____2847 =
                          let uu____2848 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2849 =
                            let uu____2850 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2851 =
                              let uu____2853 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2853] in
                            uu____2850 :: uu____2851 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2848 uu____2849 in
                        uu____2847
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2846) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2859 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2859
         then
           let uu____2860 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2861 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2862 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2860
             uu____2861 uu____2862
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
          fun uu____2884  ->
            match uu____2884 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2894 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2894
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____2897 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____2899 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2900 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2897 uu____2899 bstr uu____2900
                  else ());
                 (let bind_it uu____2905 =
                    let uu____2906 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2906
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____2916 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____2916
                        then
                          let uu____2917 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____2919 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____2920 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2921 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____2922 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____2917 uu____2919 uu____2920 uu____2921
                            uu____2922
                        else ());
                       (let try_simplify uu____2933 =
                          let aux uu____2943 =
                            let uu____2944 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2944
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____2963 ->
                                  let uu____2964 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____2964
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____2983 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____2983
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____3019 =
                                  let uu____3022 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3022, reason) in
                                FStar_Util.Inl uu____3019
                            | uu____3025 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3040 =
                              let uu____3041 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3041.FStar_Syntax_Syntax.n in
                            match uu____3040 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3045) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3051 -> c in
                          let uu____3052 =
                            let uu____3053 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3053 in
                          if uu____3052
                          then
                            let uu____3061 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3061
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3075 =
                                  let uu____3076 =
                                    let uu____3079 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3079) in
                                  FStar_Errors.Error uu____3076 in
                                raise uu____3075))
                          else
                            (let uu____3087 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3087
                             then subst_c2 "both total"
                             else
                               (let uu____3095 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3095
                                then
                                  let uu____3102 =
                                    let uu____3105 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3105, "both gtot") in
                                  FStar_Util.Inl uu____3102
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____3121 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3123 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3123) in
                                       if uu____3121
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___129_3132 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___129_3132.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___129_3132.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3133 =
                                           let uu____3136 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3136, "c1 Tot") in
                                         FStar_Util.Inl uu____3133
                                       else aux ()
                                   | uu____3140 -> aux ()))) in
                        let uu____3145 = try_simplify () in
                        match uu____3145 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3163 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3163
                              then
                                let uu____3164 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3165 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3166 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3164 uu____3165 uu____3166
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3173 = lift_and_destruct env c1 c2 in
                            (match uu____3173 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3207 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3207]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____3209 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3209] in
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
                                   let uu____3225 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3226 =
                                     let uu____3228 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3229 =
                                       let uu____3231 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3232 =
                                         let uu____3234 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3235 =
                                           let uu____3237 =
                                             let uu____3238 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3238 in
                                           [uu____3237] in
                                         uu____3234 :: uu____3235 in
                                       uu____3231 :: uu____3232 in
                                     uu____3228 :: uu____3229 in
                                   uu____3225 :: uu____3226 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3243 =
                                     let uu____3244 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3244
                                       wp_args in
                                   uu____3243 FStar_Pervasives_Native.None
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
              let uu____3295 =
                let uu____3296 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3296 in
              if uu____3295
              then f
              else (let uu____3298 = reason1 () in label uu____3298 r f)
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
            let uu___130_3312 = g in
            let uu____3313 =
              let uu____3314 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3314 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3313;
              FStar_TypeChecker_Env.deferred =
                (uu___130_3312.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___130_3312.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___130_3312.FStar_TypeChecker_Env.implicits)
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
      | uu____3326 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3346 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3350 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3350
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3357 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3357
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3362 = destruct_comp c1 in
                    match uu____3362 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3375 =
                            let uu____3376 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3377 =
                              let uu____3378 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3379 =
                                let uu____3381 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3382 =
                                  let uu____3384 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3384] in
                                uu____3381 :: uu____3382 in
                              uu____3378 :: uu____3379 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3376
                              uu____3377 in
                          uu____3375 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___131_3389 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_3389.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_3389.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_3389.FStar_Syntax_Syntax.cflags);
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
            let uu____3421 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3421
            then (lc, g0)
            else
              ((let uu____3426 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3426
                then
                  let uu____3427 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3428 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3427 uu____3428
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3435  ->
                          match uu___100_3435 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3437 -> [])) in
                let strengthen uu____3443 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3451 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3451 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3458 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3460 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3460) in
                           if uu____3458
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3467 =
                                 let uu____3468 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3468 in
                               FStar_Syntax_Util.comp_set_flags uu____3467
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3473 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3473
                           then
                             let uu____3474 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3475 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3474 uu____3475
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3478 = destruct_comp c2 in
                           match uu____3478 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3491 =
                                   let uu____3492 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3493 =
                                     let uu____3494 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3495 =
                                       let uu____3497 =
                                         let uu____3498 =
                                           let uu____3499 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3499 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3498 in
                                       let uu____3500 =
                                         let uu____3502 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3502] in
                                       uu____3497 :: uu____3500 in
                                     uu____3494 :: uu____3495 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3492
                                     uu____3493 in
                                 uu____3491 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3508 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3508
                                 then
                                   let uu____3509 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3509
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3512 =
                  let uu___132_3513 = lc in
                  let uu____3514 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3515 =
                    let uu____3517 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3519 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3519) in
                    if uu____3517 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3514;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___132_3513.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3515;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3512,
                  (let uu___133_3523 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3523.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3523.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3523.FStar_TypeChecker_Env.implicits)
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
        let uu____3541 =
          let uu____3544 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3545 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3544, uu____3545) in
        match uu____3541 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3554 =
                let uu____3555 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3556 =
                  let uu____3557 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3558 =
                    let uu____3560 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3560] in
                  uu____3557 :: uu____3558 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3555 uu____3556 in
              uu____3554 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3568 =
                let uu____3569 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3570 =
                  let uu____3571 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3572 =
                    let uu____3574 =
                      let uu____3575 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3575 in
                    let uu____3576 =
                      let uu____3578 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3578] in
                    uu____3574 :: uu____3576 in
                  uu____3571 :: uu____3572 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3569 uu____3570 in
              uu____3568 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3586 =
                let uu____3587 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3588 =
                  let uu____3589 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3590 =
                    let uu____3592 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3593 =
                      let uu____3595 =
                        let uu____3596 =
                          let uu____3597 =
                            let uu____3598 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3598] in
                          FStar_Syntax_Util.abs uu____3597 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3596 in
                      [uu____3595] in
                    uu____3592 :: uu____3593 in
                  uu____3589 :: uu____3590 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3587 uu____3588 in
              uu____3586 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3607 = FStar_TypeChecker_Env.get_range env in
              bind uu____3607 env FStar_Pervasives_Native.None
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
          let comp uu____3629 =
            let uu____3630 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3630
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3633 =
                 let uu____3646 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3647 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3646 uu____3647 in
               match uu____3633 with
               | ((md,uu____3649,uu____3650),(u_res_t,res_t,wp_then),
                  (uu____3654,uu____3655,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3684 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3685 =
                       let uu____3686 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3687 =
                         let uu____3688 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3689 =
                           let uu____3691 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3692 =
                             let uu____3694 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3695 =
                               let uu____3697 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3697] in
                             uu____3694 :: uu____3695 in
                           uu____3691 :: uu____3692 in
                         uu____3688 :: uu____3689 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3686 uu____3687 in
                     uu____3685 FStar_Pervasives_Native.None uu____3684 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3705 =
                     let uu____3706 = FStar_Options.split_cases () in
                     uu____3706 > (Prims.parse_int "0") in
                   if uu____3705
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3712 =
                          let uu____3713 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3714 =
                            let uu____3715 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3716 =
                              let uu____3718 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3718] in
                            uu____3715 :: uu____3716 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3713 uu____3714 in
                        uu____3712 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3723 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3723;
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
      let uu____3732 =
        let uu____3733 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3733 in
      FStar_Syntax_Syntax.fvar uu____3732 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3760  ->
                 match uu____3760 with
                 | (uu____3763,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____3768 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3770 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3770
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3790 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3791 =
                 let uu____3792 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3793 =
                   let uu____3794 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3795 =
                     let uu____3797 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3798 =
                       let uu____3800 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3801 =
                         let uu____3803 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3803] in
                       uu____3800 :: uu____3801 in
                     uu____3797 :: uu____3798 in
                   uu____3794 :: uu____3795 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3792 uu____3793 in
               uu____3791 FStar_Pervasives_Native.None uu____3790 in
             let default_case =
               let post_k =
                 let uu____3812 =
                   let uu____3816 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3816] in
                 let uu____3817 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3812 uu____3817 in
               let kwp =
                 let uu____3823 =
                   let uu____3827 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3827] in
                 let uu____3828 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3823 uu____3828 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____3833 =
                   let uu____3834 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3834] in
                 let uu____3835 =
                   let uu____3836 =
                     let uu____3839 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3839 in
                   let uu____3840 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____3836 uu____3840 in
                 FStar_Syntax_Util.abs uu____3833 uu____3835
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
                 (fun uu____3862  ->
                    fun celse  ->
                      match uu____3862 with
                      | (g,cthen) ->
                          let uu____3868 =
                            let uu____3881 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3881 celse in
                          (match uu____3868 with
                           | ((md,uu____3883,uu____3884),(uu____3885,uu____3886,wp_then),
                              (uu____3888,uu____3889,wp_else)) ->
                               let uu____3900 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3900 []))
                 lcases default_case in
             let uu____3901 =
               let uu____3902 = FStar_Options.split_cases () in
               uu____3902 > (Prims.parse_int "0") in
             if uu____3901
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3906 = destruct_comp comp1 in
                match uu____3906 with
                | (uu____3910,uu____3911,wp) ->
                    let wp1 =
                      let uu____3916 =
                        let uu____3917 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3918 =
                          let uu____3919 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3920 =
                            let uu____3922 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3922] in
                          uu____3919 :: uu____3920 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3917 uu____3918 in
                      uu____3916 FStar_Pervasives_Native.None
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
          let uu____3941 =
            ((let uu____3944 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____3944) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3946 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____3946) in
          if uu____3941
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____3954 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3958 =
            (let uu____3961 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____3961) || env.FStar_TypeChecker_Env.lax in
          if uu____3958
          then c
          else
            (let uu____3965 = FStar_Syntax_Util.is_partial_return c in
             if uu____3965
             then c
             else
               (let uu____3969 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____3969
                then
                  let uu____3972 =
                    let uu____3973 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____3973 in
                  (if uu____3972
                   then
                     let uu____3976 =
                       let uu____3977 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____3978 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____3977 uu____3978 in
                     failwith uu____3976
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____3983 =
                        let uu____3984 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____3984 in
                      if uu____3983
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___134_3989 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___134_3989.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___134_3989.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___134_3989.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4000 =
                       let uu____4003 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4003
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4000 in
                   let eq1 =
                     let uu____4007 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4007 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4009 =
                     let uu____4010 =
                       let uu____4015 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____4015.FStar_Syntax_Syntax.comp in
                     uu____4010 () in
                   FStar_Syntax_Util.comp_set_flags uu____4009 flags))) in
        let uu___135_4017 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___135_4017.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___135_4017.FStar_Syntax_Syntax.res_typ);
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
          let uu____4040 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4040 with
          | FStar_Pervasives_Native.None  ->
              let uu____4045 =
                let uu____4046 =
                  let uu____4049 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4050 = FStar_TypeChecker_Env.get_range env in
                  (uu____4049, uu____4050) in
                FStar_Errors.Error uu____4046 in
              raise uu____4045
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
            let uu____4080 =
              let uu____4081 = FStar_Syntax_Subst.compress t2 in
              uu____4081.FStar_Syntax_Syntax.n in
            match uu____4080 with
            | FStar_Syntax_Syntax.Tm_type uu____4084 -> true
            | uu____4085 -> false in
          let uu____4086 =
            let uu____4087 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4087.FStar_Syntax_Syntax.n in
          match uu____4086 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4093 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____4100 =
                  let uu____4101 =
                    let uu____4102 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4102 in
                  (FStar_Pervasives_Native.None, uu____4101) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____4100 in
              let e1 =
                let uu____4111 =
                  let uu____4112 =
                    let uu____4113 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4113] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4112 in
                uu____4111
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4120 -> (e, lc)
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
              (let uu____4147 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4147 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4160 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4172 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4172, false)
            else
              (let uu____4176 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4176, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____4182) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___136_4186 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___136_4186.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___136_4186.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___136_4186.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____4190 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4190 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___137_4195 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___137_4195.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___137_4195.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___137_4195.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___138_4198 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___138_4198.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___138_4198.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___138_4198.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4204 =
                     let uu____4205 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4205
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____4210 =
                          let uu____4211 = FStar_Syntax_Subst.compress f1 in
                          uu____4211.FStar_Syntax_Syntax.n in
                        match uu____4210 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4216,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4218;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4219;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4220;_},uu____4221)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___139_4235 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___139_4235.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___139_4235.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___139_4235.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4236 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4241 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4241
                              then
                                let uu____4242 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4243 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4244 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4245 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4242 uu____4243 uu____4244 uu____4245
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4248 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____4248 with
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
                                  let uu____4259 = destruct_comp ct in
                                  (match uu____4259 with
                                   | (u_t,uu____4266,uu____4267) ->
                                       let wp =
                                         let uu____4271 =
                                           let uu____4272 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4273 =
                                             let uu____4274 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4275 =
                                               let uu____4277 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4277] in
                                             uu____4274 :: uu____4275 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4272 uu____4273 in
                                         uu____4271
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4283 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4283 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4293 =
                                             let uu____4294 =
                                               let uu____4295 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4295] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4294 in
                                           uu____4293
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4301 =
                                         let uu____4304 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4315 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4316 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4304
                                           uu____4315 e cret uu____4316 in
                                       (match uu____4301 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___140_4322 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___140_4322.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___140_4322.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4324 =
                                                let uu____4325 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4325 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____4324
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4335 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4335
                                              then
                                                let uu____4336 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4336
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4343  ->
                             match uu___101_4343 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4345 -> [])) in
                   let lc1 =
                     let uu___141_4347 = lc in
                     let uu____4348 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4348;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___142_4350 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___142_4350.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___142_4350.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___142_4350.FStar_TypeChecker_Env.implicits)
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
        let uu____4372 =
          let uu____4373 =
            let uu____4374 =
              let uu____4375 =
                let uu____4376 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4376 in
              [uu____4375] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4374 in
          uu____4373 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4372 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4385 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4385
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4396 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4405 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4422)::(ens,uu____4424)::uu____4425 ->
                    let uu____4447 =
                      let uu____4449 = norm req in
                      FStar_Pervasives_Native.Some uu____4449 in
                    let uu____4450 =
                      let uu____4451 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4451 in
                    (uu____4447, uu____4450)
                | uu____4453 ->
                    let uu____4459 =
                      let uu____4460 =
                        let uu____4463 =
                          let uu____4464 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4464 in
                        (uu____4463, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4460 in
                    raise uu____4459)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4474)::uu____4475 ->
                    let uu____4489 =
                      let uu____4492 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____4492 in
                    (match uu____4489 with
                     | (us_r,uu____4509) ->
                         let uu____4510 =
                           let uu____4513 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____4513 in
                         (match uu____4510 with
                          | (us_e,uu____4530) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4533 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4533
                                  us_r in
                              let as_ens =
                                let uu____4535 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4535
                                  us_e in
                              let req =
                                let uu____4539 =
                                  let uu____4540 =
                                    let uu____4541 =
                                      let uu____4548 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4548] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4541 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4540 in
                                uu____4539
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4564 =
                                  let uu____4565 =
                                    let uu____4566 =
                                      let uu____4573 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4573] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4566 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4565 in
                                uu____4564 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4586 =
                                let uu____4588 = norm req in
                                FStar_Pervasives_Native.Some uu____4588 in
                              let uu____4589 =
                                let uu____4590 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4590 in
                              (uu____4586, uu____4589)))
                | uu____4592 -> failwith "Impossible"))
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
      (let uu____4614 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4614
       then
         let uu____4615 = FStar_Syntax_Print.term_to_string tm in
         let uu____4616 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4615 uu____4616
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
        (let uu____4640 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4640
         then
           let uu____4641 = FStar_Syntax_Print.term_to_string tm in
           let uu____4642 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4641
             uu____4642
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4648 =
      let uu____4649 =
        let uu____4650 = FStar_Syntax_Subst.compress t in
        uu____4650.FStar_Syntax_Syntax.n in
      match uu____4649 with
      | FStar_Syntax_Syntax.Tm_app uu____4653 -> false
      | uu____4663 -> true in
    if uu____4648
    then t
    else
      (let uu____4665 = FStar_Syntax_Util.head_and_args t in
       match uu____4665 with
       | (head1,args) ->
           let uu____4691 =
             let uu____4692 =
               let uu____4693 = FStar_Syntax_Subst.compress head1 in
               uu____4693.FStar_Syntax_Syntax.n in
             match uu____4692 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4696 -> false in
           if uu____4691
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____4712 ->
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
             let uu____4743 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4743 with
             | (formals,uu____4752) ->
                 let n_implicits =
                   let uu____4764 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4804  ->
                             match uu____4804 with
                             | (uu____4808,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____4764 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4883 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4883 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4904 =
                     let uu____4905 =
                       let uu____4908 =
                         let uu____4909 = FStar_Util.string_of_int n_expected in
                         let uu____4916 = FStar_Syntax_Print.term_to_string e in
                         let uu____4917 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4909 uu____4916 uu____4917 in
                       let uu____4924 = FStar_TypeChecker_Env.get_range env in
                       (uu____4908, uu____4924) in
                     FStar_Errors.Error uu____4905 in
                   raise uu____4904
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___102_4942 =
             match uu___102_4942 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4961 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4961 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____5022) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5044,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5063 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5063 with
                           | (v1,uu____5084,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5094 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5094 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5143 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5143)))
                      | (uu____5157,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5181 =
                      let uu____5195 = inst_n_binders t in
                      aux [] uu____5195 bs1 in
                    (match uu____5181 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5233) -> (e, torig, guard)
                          | (uu____5249,[]) when
                              let uu____5265 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5265 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5266 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5285 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5298 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5305 =
      let uu____5307 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5307
        (FStar_List.map
           (fun u  ->
              let uu____5314 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5314 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5305 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5328 = FStar_Util.set_is_empty x in
      if uu____5328
      then []
      else
        (let s =
           let uu____5333 =
             let uu____5335 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5335 in
           FStar_All.pipe_right uu____5333 FStar_Util.set_elements in
         (let uu____5340 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5340
          then
            let uu____5341 =
              let uu____5342 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5342 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5341
          else ());
         (let r =
            let uu____5347 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____5347 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5359 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5359
                     then
                       let uu____5360 =
                         let uu____5361 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5361 in
                       let uu____5362 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5363 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5360 uu____5362 uu____5363
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
        let uu____5382 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5382 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_5412 =
  match uu___103_5412 with
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
        | ([],uu____5455) -> generalized_univ_names
        | (uu____5459,[]) -> explicit_univ_names
        | uu____5463 ->
            let uu____5468 =
              let uu____5469 =
                let uu____5472 =
                  let uu____5473 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5473 in
                (uu____5472, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5469 in
            raise uu____5468
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
      (let uu____5489 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5489
       then
         let uu____5490 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5490
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5495 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5495
        then
          let uu____5496 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5496
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____5502 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5502))
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
      let uu____5534 =
        let uu____5535 =
          FStar_Util.for_all
            (fun uu____5543  ->
               match uu____5543 with
               | (uu____5548,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5535 in
      if uu____5534
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____5571 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5571
            then
              let uu____5572 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5572
            else ());
           (let c1 =
              let uu____5575 = FStar_TypeChecker_Env.should_verify env in
              if uu____5575
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
            (let uu____5578 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5578
             then
               let uu____5579 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5579
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5619 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5619 FStar_Util.set_elements in
         let uu____5673 =
           let uu____5693 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5766  ->
                     match uu____5766 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____5808 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____5808
                           then
                             let uu____5809 =
                               let uu____5810 =
                                 let uu____5812 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____5812
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____5810
                                 (FStar_String.concat ", ") in
                             let uu____5827 =
                               let uu____5828 =
                                 let uu____5830 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____5830
                                   (FStar_List.map
                                      (fun uu____5847  ->
                                         match uu____5847 with
                                         | (u,t2) ->
                                             let uu____5852 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____5853 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____5852 uu____5853)) in
                               FStar_All.pipe_right uu____5828
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____5809 uu____5827
                           else ());
                          (let univs2 =
                             let uu____5858 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____5873  ->
                                    match uu____5873 with
                                    | (uu____5878,t2) ->
                                        let uu____5880 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____5880) univs1 uu____5858 in
                           let uvs = gen_uvars uvt in
                           (let uu____5895 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____5895
                            then
                              let uu____5896 =
                                let uu____5897 =
                                  let uu____5899 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____5899
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____5897
                                  (FStar_String.concat ", ") in
                              let uu____5914 =
                                let uu____5915 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____5936  ->
                                          match uu____5936 with
                                          | (u,t2) ->
                                              let uu____5941 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____5942 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____5941 uu____5942)) in
                                FStar_All.pipe_right uu____5915
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____5896 uu____5914
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____5693 FStar_List.unzip in
         match uu____5673 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____6067 = FStar_List.hd univs1 in
               let uu____6070 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____6083 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____6083
                      then out
                      else
                        (let uu____6086 =
                           let uu____6087 =
                             let uu____6090 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____6090) in
                           FStar_Errors.Error uu____6087 in
                         raise uu____6086)) uu____6067 uu____6070 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6095 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6095
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
                      (fun uu____6144  ->
                         match uu____6144 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6189  ->
                                       match uu____6189 with
                                       | (u,k) ->
                                           let uu____6197 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6197 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6203;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6204;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6205;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6211,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6213;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6214;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6215;_},uu____6216);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6217;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6218;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6219;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____6237 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6241 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____6244 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6244 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6268 =
                                                         let uu____6270 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____6270 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6268 kres in
                                                     let t =
                                                       let uu____6273 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6273
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6276 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____6294 ->
                                   let uu____6302 = (e, c) in
                                   (match uu____6302 with
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
                                          let uu____6314 =
                                            let uu____6315 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6315.FStar_Syntax_Syntax.n in
                                          match uu____6314 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6332 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6332 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6342 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____6344 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6344)) in
                             (match uu____6276 with
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
      (let uu____6384 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6384
       then
         let uu____6385 =
           let uu____6386 =
             FStar_List.map
               (fun uu____6395  ->
                  match uu____6395 with
                  | (lb,uu____6400,uu____6401) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6386 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6385
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6415  ->
              match uu____6415 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6430 =
           let uu____6437 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6457  ->
                     match uu____6457 with | (uu____6463,e,c) -> (e, c))) in
           gen env uu____6437 in
         match uu____6430 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6499  ->
                     match uu____6499 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____6552  ->
                  fun uu____6553  ->
                    match (uu____6552, uu____6553) with
                    | ((l,uu____6586,uu____6587),(us,e,c)) ->
                        ((let uu____6613 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6613
                          then
                            let uu____6614 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6615 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6616 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6617 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6614 uu____6615 uu____6616 uu____6617
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6643  ->
              match uu____6643 with
              | (l,generalized_univs,t,c) ->
                  let uu____6661 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6661, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6698 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6698 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____6702 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____6702) in
          let is_var e1 =
            let uu____6708 =
              let uu____6709 = FStar_Syntax_Subst.compress e1 in
              uu____6709.FStar_Syntax_Syntax.n in
            match uu____6708 with
            | FStar_Syntax_Syntax.Tm_name uu____6712 -> true
            | uu____6713 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___143_6733 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___143_6733.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___143_6733.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6734 ->
                let uu___144_6735 = e2 in
                let uu____6736 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_6735.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6736;
                  FStar_Syntax_Syntax.pos =
                    (uu___144_6735.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___144_6735.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___145_6745 = env1 in
            let uu____6746 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___145_6745.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___145_6745.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___145_6745.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___145_6745.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___145_6745.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___145_6745.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___145_6745.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___145_6745.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___145_6745.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___145_6745.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___145_6745.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___145_6745.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___145_6745.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___145_6745.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___145_6745.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6746;
              FStar_TypeChecker_Env.is_iface =
                (uu___145_6745.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___145_6745.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___145_6745.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___145_6745.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___145_6745.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___145_6745.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___145_6745.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___145_6745.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___145_6745.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___145_6745.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___145_6745.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6747 = check env2 t1 t2 in
          match uu____6747 with
          | FStar_Pervasives_Native.None  ->
              let uu____6751 =
                let uu____6752 =
                  let uu____6755 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6756 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6755, uu____6756) in
                FStar_Errors.Error uu____6752 in
              raise uu____6751
          | FStar_Pervasives_Native.Some g ->
              ((let uu____6761 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6761
                then
                  let uu____6762 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6762
                else ());
               (let uu____6764 = decorate e t2 in (uu____6764, g)))
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
        let uu____6791 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6791
        then
          let uu____6794 = discharge g1 in
          let uu____6795 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6794, uu____6795)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6807 =
               let uu____6808 =
                 let uu____6809 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6809 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6808
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6807
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6811 = destruct_comp c1 in
           match uu____6811 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6823 = FStar_TypeChecker_Env.get_range env in
                 let uu____6824 =
                   let uu____6825 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6826 =
                     let uu____6827 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6828 =
                       let uu____6830 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6830] in
                     uu____6827 :: uu____6828 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6825 uu____6826 in
                 uu____6824
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6823 in
               ((let uu____6836 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6836
                 then
                   let uu____6837 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6837
                 else ());
                (let g2 =
                   let uu____6840 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6840 in
                 let uu____6841 = discharge g2 in
                 let uu____6842 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6841, uu____6842))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6868 =
        match uu___104_6868 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6874)::[] -> f fst1
        | uu____6887 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6892 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6892
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6901 =
          let uu____6904 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6904 in
        FStar_All.pipe_right uu____6901
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6915 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6915
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_6929 =
        match uu___105_6929 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6935)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6950)::[] ->
            let uu____6971 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6971
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6976 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6983 =
          let uu____6988 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____6988) in
        let uu____6993 =
          let uu____6999 =
            let uu____7004 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____7004) in
          let uu____7009 =
            let uu____7015 =
              let uu____7020 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____7020) in
            let uu____7025 =
              let uu____7031 =
                let uu____7036 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____7036) in
              let uu____7041 =
                let uu____7047 =
                  let uu____7052 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____7052) in
                [uu____7047; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____7031 :: uu____7041 in
            uu____7015 :: uu____7025 in
          uu____6999 :: uu____7009 in
        uu____6983 :: uu____6993 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7089 =
            FStar_Util.find_map table
              (fun uu____7099  ->
                 match uu____7099 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____7112 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____7112
                     else FStar_Pervasives_Native.None) in
          (match uu____7089 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____7115 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7120 =
      let uu____7121 = FStar_Syntax_Util.un_uinst l in
      uu____7121.FStar_Syntax_Syntax.n in
    match uu____7120 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____7125 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7145)::uu____7146 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7152 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7156,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____7157))::uu____7158 -> bs
      | uu____7167 ->
          let uu____7168 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7168 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____7171 =
                 let uu____7172 = FStar_Syntax_Subst.compress t in
                 uu____7172.FStar_Syntax_Syntax.n in
               (match uu____7171 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7176) ->
                    let uu____7187 =
                      FStar_Util.prefix_until
                        (fun uu___106_7209  ->
                           match uu___106_7209 with
                           | (uu____7213,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7214)) ->
                               false
                           | uu____7216 -> true) bs' in
                    (match uu____7187 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____7234,uu____7235) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____7272,uu____7273) ->
                         let uu____7310 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7321  ->
                                   match uu____7321 with
                                   | (x,uu____7326) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7310
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7353  ->
                                     match uu____7353 with
                                     | (x,i) ->
                                         let uu____7364 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7364, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7370 -> bs))
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
              (let uu____7394 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7394 e.FStar_Syntax_Syntax.pos)
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
          let uu____7420 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____7420
          then e
          else
            (let uu____7422 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7422
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
        (let uu____7452 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7452
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7454 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7454))
         else ());
        (let fv =
           let uu____7457 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7457
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
         let uu____7463 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___146_7473 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___146_7473.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___146_7473.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___146_7473.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___146_7473.FStar_Syntax_Syntax.sigattrs)
           }), uu____7463))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7485 =
        match uu___107_7485 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7486 -> false in
      let reducibility uu___108_7490 =
        match uu___108_7490 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7491 -> false in
      let assumption uu___109_7495 =
        match uu___109_7495 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7496 -> false in
      let reification uu___110_7500 =
        match uu___110_7500 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7501 -> true
        | uu____7502 -> false in
      let inferred uu___111_7506 =
        match uu___111_7506 with
        | FStar_Syntax_Syntax.Discriminator uu____7507 -> true
        | FStar_Syntax_Syntax.Projector uu____7508 -> true
        | FStar_Syntax_Syntax.RecordType uu____7511 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7516 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7521 -> false in
      let has_eq uu___112_7525 =
        match uu___112_7525 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7526 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7572 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7576 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7579 =
        let uu____7580 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7583  ->
                  match uu___113_7583 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7584 -> false)) in
        FStar_All.pipe_right uu____7580 Prims.op_Negation in
      if uu____7579
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7596 =
            let uu____7597 =
              let uu____7600 =
                let uu____7601 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7601 msg in
              (uu____7600, r) in
            FStar_Errors.Error uu____7597 in
          raise uu____7596 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7609 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7621 =
            let uu____7622 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7622 in
          if uu____7621 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____7626),uu____7627) ->
              ((let uu____7636 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7636
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7639 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7639
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7644 ->
              let uu____7649 =
                let uu____7650 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7650 in
              if uu____7649 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7655 ->
              let uu____7659 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7659 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7662 ->
              let uu____7666 =
                let uu____7667 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7667 in
              if uu____7666 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7672 ->
              let uu____7673 =
                let uu____7674 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7674 in
              if uu____7673 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7679 ->
              let uu____7680 =
                let uu____7681 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7681 in
              if uu____7680 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7686 ->
              let uu____7693 =
                let uu____7694 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7694 in
              if uu____7693 then err'1 () else ()
          | uu____7699 -> ()))
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
                          let uu____7766 =
                            let uu____7769 =
                              let uu____7770 =
                                let uu____7775 =
                                  let uu____7776 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7776 in
                                (uu____7775, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7770 in
                            FStar_Syntax_Syntax.mk uu____7769 in
                          uu____7766 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7806  ->
                                  match uu____7806 with
                                  | (x,imp) ->
                                      let uu____7813 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7813, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7817 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7817 in
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
                             let uu____7826 =
                               let uu____7827 =
                                 let uu____7828 =
                                   let uu____7829 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7830 =
                                     let uu____7831 =
                                       let uu____7832 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7832 in
                                     [uu____7831] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7829
                                     uu____7830 in
                                 uu____7828 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7827 in
                             FStar_Syntax_Util.refine x uu____7826 in
                           let uu____7837 =
                             let uu___147_7838 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___147_7838.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___147_7838.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7837) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7849 =
                          FStar_List.map
                            (fun uu____7862  ->
                               match uu____7862 with
                               | (x,uu____7869) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7849 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7896  ->
                                match uu____7896 with
                                | (x,uu____7903) ->
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
                             (let uu____7914 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____7914)
                               ||
                               (let uu____7916 =
                                  let uu____7917 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7917.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7916) in
                           let quals =
                             let uu____7920 =
                               let uu____7922 =
                                 let uu____7924 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7924
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7927 =
                                 FStar_List.filter
                                   (fun uu___114_7930  ->
                                      match uu___114_7930 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7931 -> false) iquals in
                               FStar_List.append uu____7922 uu____7927 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7920 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7944 =
                                 let uu____7945 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7945 in
                               FStar_Syntax_Syntax.mk_Total uu____7944 in
                             let uu____7946 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7946 in
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
                           (let uu____7949 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7949
                            then
                              let uu____7950 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7950
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
                                             fun uu____7985  ->
                                               match uu____7985 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____8001 =
                                                       let uu____8003 =
                                                         let uu____8004 =
                                                           let uu____8009 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____8009,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8004 in
                                                       pos uu____8003 in
                                                     (uu____8001, b)
                                                   else
                                                     (let uu____8012 =
                                                        let uu____8014 =
                                                          let uu____8015 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8015 in
                                                        pos uu____8014 in
                                                      (uu____8012, b)))) in
                                   let pat_true =
                                     let uu____8027 =
                                       let uu____8029 =
                                         let uu____8030 =
                                           let uu____8037 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____8037, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8030 in
                                       pos uu____8029 in
                                     (uu____8027,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____8060 =
                                       let uu____8062 =
                                         let uu____8063 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8063 in
                                       pos uu____8062 in
                                     (uu____8060,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____8073 =
                                     let uu____8076 =
                                       let uu____8077 =
                                         let uu____8092 =
                                           let uu____8094 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8095 =
                                             let uu____8097 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8097] in
                                           uu____8094 :: uu____8095 in
                                         (arg_exp, uu____8092) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8077 in
                                     FStar_Syntax_Syntax.mk uu____8076 in
                                   uu____8073 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____8108 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8108
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
                                let uu____8115 =
                                  let uu____8118 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____8118 in
                                let uu____8119 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____8115;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____8119
                                } in
                              let impl =
                                let uu____8123 =
                                  let uu____8124 =
                                    let uu____8128 =
                                      let uu____8130 =
                                        let uu____8131 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8131
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8130] in
                                    ((false, [lb]), uu____8128) in
                                  FStar_Syntax_Syntax.Sig_let uu____8124 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8123;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____8142 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8142
                               then
                                 let uu____8143 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8143
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
                                fun uu____8172  ->
                                  match uu____8172 with
                                  | (a,uu____8176) ->
                                      let uu____8177 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8177 with
                                       | (field_name,uu____8181) ->
                                           let field_proj_tm =
                                             let uu____8183 =
                                               let uu____8184 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8184 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8183 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8198 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8222  ->
                                    match uu____8222 with
                                    | (x,uu____8227) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8229 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8229 with
                                         | (field_name,uu____8234) ->
                                             let t =
                                               let uu____8236 =
                                                 let uu____8237 =
                                                   let uu____8240 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8240 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8237 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8236 in
                                             let only_decl =
                                               (let uu____8244 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____8244)
                                                 ||
                                                 (let uu____8246 =
                                                    let uu____8247 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8247.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8246) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8257 =
                                                   FStar_List.filter
                                                     (fun uu___115_8260  ->
                                                        match uu___115_8260
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8261 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8257
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_8270  ->
                                                         match uu___116_8270
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8271 ->
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
                                             ((let uu____8274 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8274
                                               then
                                                 let uu____8275 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8275
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
                                                           fun uu____8305  ->
                                                             match uu____8305
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8321
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8321,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8332
                                                                    =
                                                                    let uu____8334
                                                                    =
                                                                    let uu____8335
                                                                    =
                                                                    let uu____8340
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8340,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8335 in
                                                                    pos
                                                                    uu____8334 in
                                                                    (uu____8332,
                                                                    b))
                                                                   else
                                                                    (let uu____8343
                                                                    =
                                                                    let uu____8345
                                                                    =
                                                                    let uu____8346
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8346 in
                                                                    pos
                                                                    uu____8345 in
                                                                    (uu____8343,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8356 =
                                                     let uu____8358 =
                                                       let uu____8359 =
                                                         let uu____8366 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8366,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8359 in
                                                     pos uu____8358 in
                                                   let uu____8371 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8356,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8371) in
                                                 let body =
                                                   let uu____8381 =
                                                     let uu____8384 =
                                                       let uu____8385 =
                                                         let uu____8400 =
                                                           let uu____8402 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8402] in
                                                         (arg_exp,
                                                           uu____8400) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8385 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8384 in
                                                   uu____8381
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8414 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8414
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
                                                   let uu____8420 =
                                                     let uu____8423 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8423 in
                                                   let uu____8424 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8420;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8424
                                                   } in
                                                 let impl =
                                                   let uu____8428 =
                                                     let uu____8429 =
                                                       let uu____8433 =
                                                         let uu____8435 =
                                                           let uu____8436 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8436
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8435] in
                                                       ((false, [lb]),
                                                         uu____8433) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8429 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8428;
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
                                                 (let uu____8447 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8447
                                                  then
                                                    let uu____8448 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8448
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8198 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8482) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____8485 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8485 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8498 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8498 with
                    | (formals,uu____8508) ->
                        let uu____8519 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8541 =
                                   let uu____8542 =
                                     let uu____8543 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8543 in
                                   FStar_Ident.lid_equals typ_lid uu____8542 in
                                 if uu____8541
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8553,uvs',tps,typ0,uu____8557,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8574 -> failwith "Impossible"
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
                        (match uu____8519 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8616 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8616 with
                              | (indices,uu____8626) ->
                                  let refine_domain =
                                    let uu____8638 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_8642  ->
                                              match uu___117_8642 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8643 -> true
                                              | uu____8648 -> false)) in
                                    if uu____8638
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_8655 =
                                      match uu___118_8655 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8657,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8664 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8665 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8665 with
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
                                    let uu____8673 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8673 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8711  ->
                                               fun uu____8712  ->
                                                 match (uu____8711,
                                                         uu____8712)
                                                 with
                                                 | ((x,uu____8722),(x',uu____8724))
                                                     ->
                                                     let uu____8729 =
                                                       let uu____8734 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8734) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8729) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8735 -> []