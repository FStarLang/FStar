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
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_1726 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_1726.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_1726.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1730 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1730
                then
                  let uu____1731 =
                    let uu____1732 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1733 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1732 uu____1733 in
                  failwith uu____1731
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_1737 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1737.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1737.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1739),uu____1740) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1755 =
                  let uu____1756 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1756 in
                if uu____1755
                then
                  let uu____1757 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1757
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1769;
                FStar_Syntax_Syntax.pos = uu____1770;
                FStar_Syntax_Syntax.vars = uu____1771;_},args))
              ->
              ((let uu____1796 =
                  let uu____1797 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1797 Prims.op_Negation in
                if uu____1796
                then
                  let uu____1798 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1798
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1879)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1923) ->
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
                       | ((e2,imp),uu____1949) ->
                           let pat =
                             let uu____1964 = aux argpat e2 in
                             let uu____1965 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____1964, uu____1965) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1968 ->
                      let uu____1981 =
                        let uu____1982 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____1983 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1982 uu____1983 in
                      failwith uu____1981 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____1991;
                     FStar_Syntax_Syntax.pos = uu____1992;
                     FStar_Syntax_Syntax.vars = uu____1993;_},uu____1994);
                FStar_Syntax_Syntax.tk = uu____1995;
                FStar_Syntax_Syntax.pos = uu____1996;
                FStar_Syntax_Syntax.vars = uu____1997;_},args))
              ->
              ((let uu____2026 =
                  let uu____2027 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2027 Prims.op_Negation in
                if uu____2026
                then
                  let uu____2028 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2028
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2109)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2153) ->
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
                       | ((e2,imp),uu____2179) ->
                           let pat =
                             let uu____2194 = aux argpat e2 in
                             let uu____2195 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2194, uu____2195) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2198 ->
                      let uu____2211 =
                        let uu____2212 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2213 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2212 uu____2213 in
                      failwith uu____2211 in
                match_args [] args argpats))
          | uu____2218 ->
              let uu____2221 =
                let uu____2222 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2223 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2224 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2222 uu____2223 uu____2224 in
              failwith uu____2221 in
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
    let pat_as_arg uu____2253 =
      match uu____2253 with
      | (p,i) ->
          let uu____2263 = decorated_pattern_as_term p in
          (match uu____2263 with
           | (vars,te) ->
               let uu____2276 =
                 let uu____2279 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2279) in
               (vars, uu____2276)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2287 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2287)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2290 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2290)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2293 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2293)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2305 =
          let uu____2313 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2313 FStar_List.unzip in
        (match uu____2305 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2370 =
               let uu____2371 =
                 let uu____2372 =
                   let uu____2382 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2382, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2372 in
               mk1 uu____2371 in
             (vars1, uu____2370))
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
      | (wp,uu____2412)::[] -> wp
      | uu____2425 ->
          let uu____2431 =
            let uu____2432 =
              let uu____2433 =
                FStar_List.map
                  (fun uu____2440  ->
                     match uu____2440 with
                     | (x,uu____2444) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2433 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2432 in
          failwith uu____2431 in
    let uu____2448 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2448, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2465 = destruct_comp c in
        match uu____2465 with
        | (u,uu____2470,wp) ->
            let uu____2472 =
              let uu____2478 =
                let uu____2479 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2479 in
              [uu____2478] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2472;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2492 =
          let uu____2496 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2497 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2496 uu____2497 in
        match uu____2492 with | (m,uu____2499,uu____2500) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2513 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2513
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
        let uu____2541 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2541 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2563 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2563 with
             | (a,kwp) ->
                 let uu____2580 = destruct_comp m1 in
                 let uu____2584 = destruct_comp m2 in
                 ((md, a, kwp), uu____2580, uu____2584))
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
            let uu____2641 =
              let uu____2642 =
                let uu____2648 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2648] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2642;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2641
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
      let uu___129_2695 = lc in
      let uu____2696 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___129_2695.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2696;
        FStar_Syntax_Syntax.cflags =
          (uu___129_2695.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2701  ->
             let uu____2702 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2702)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2707 =
      let uu____2708 = FStar_Syntax_Subst.compress t in
      uu____2708.FStar_Syntax_Syntax.n in
    match uu____2707 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2711 -> true
    | uu____2719 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2734 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2734
        then c
        else
          (let uu____2736 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2736
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2772 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2772] in
                       let us =
                         let uu____2775 =
                           let uu____2777 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2777] in
                         u_res :: uu____2775 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2781 =
                         let uu____2782 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2783 =
                           let uu____2784 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2785 =
                             let uu____2787 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2788 =
                               let uu____2790 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2790] in
                             uu____2787 :: uu____2788 in
                           uu____2784 :: uu____2785 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2782 uu____2783 in
                       uu____2781 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2796 = destruct_comp c1 in
              match uu____2796 with
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
        let close1 uu____2822 =
          let uu____2823 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2823 in
        let uu___130_2824 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___130_2824.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___130_2824.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___130_2824.FStar_Syntax_Syntax.cflags);
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
          let uu____2838 =
            let uu____2839 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2839 in
          if uu____2838
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2844 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2844
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2846 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____2846 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2852 =
                        let uu____2853 =
                          let uu____2854 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2855 =
                            let uu____2856 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2857 =
                              let uu____2859 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2859] in
                            uu____2856 :: uu____2857 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2854 uu____2855 in
                        uu____2853
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2852) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2865 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2865
         then
           let uu____2866 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2867 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2868 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2866
             uu____2867 uu____2868
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
          fun uu____2890  ->
            match uu____2890 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2900 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2900
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____2903 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____2905 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2906 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2903 uu____2905 bstr uu____2906
                  else ());
                 (let bind_it uu____2911 =
                    let uu____2912 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2912
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____2922 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____2922
                        then
                          let uu____2923 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____2925 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____2926 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2927 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____2928 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____2923 uu____2925 uu____2926 uu____2927
                            uu____2928
                        else ());
                       (let try_simplify uu____2939 =
                          let aux uu____2949 =
                            let uu____2950 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2950
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____2969 ->
                                  let uu____2970 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____2970
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____2989 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____2989
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____3025 =
                                  let uu____3028 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3028, reason) in
                                FStar_Util.Inl uu____3025
                            | uu____3031 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3046 =
                              let uu____3047 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3047.FStar_Syntax_Syntax.n in
                            match uu____3046 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3051) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3057 -> c in
                          let uu____3058 =
                            let uu____3059 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3059 in
                          if uu____3058
                          then
                            let uu____3067 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3067
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3081 =
                                  let uu____3082 =
                                    let uu____3085 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3085) in
                                  FStar_Errors.Error uu____3082 in
                                raise uu____3081))
                          else
                            (let uu____3093 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3093
                             then subst_c2 "both total"
                             else
                               (let uu____3101 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3101
                                then
                                  let uu____3108 =
                                    let uu____3111 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3111, "both gtot") in
                                  FStar_Util.Inl uu____3108
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____3127 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3129 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3129) in
                                       if uu____3127
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___131_3138 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___131_3138.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___131_3138.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3139 =
                                           let uu____3142 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3142, "c1 Tot") in
                                         FStar_Util.Inl uu____3139
                                       else aux ()
                                   | uu____3146 -> aux ()))) in
                        let uu____3151 = try_simplify () in
                        match uu____3151 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3169 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3169
                              then
                                let uu____3170 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3171 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3172 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3170 uu____3171 uu____3172
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3179 = lift_and_destruct env c1 c2 in
                            (match uu____3179 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3213 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3213]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____3215 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3215] in
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
                                   let uu____3231 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3232 =
                                     let uu____3234 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3235 =
                                       let uu____3237 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3238 =
                                         let uu____3240 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3241 =
                                           let uu____3243 =
                                             let uu____3244 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3244 in
                                           [uu____3243] in
                                         uu____3240 :: uu____3241 in
                                       uu____3237 :: uu____3238 in
                                     uu____3234 :: uu____3235 in
                                   uu____3231 :: uu____3232 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3249 =
                                     let uu____3250 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3250
                                       wp_args in
                                   uu____3249 FStar_Pervasives_Native.None
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
              let uu____3301 =
                let uu____3302 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3302 in
              if uu____3301
              then f
              else (let uu____3304 = reason1 () in label uu____3304 r f)
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
            let uu___132_3318 = g in
            let uu____3319 =
              let uu____3320 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3320 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3319;
              FStar_TypeChecker_Env.deferred =
                (uu___132_3318.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_3318.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_3318.FStar_TypeChecker_Env.implicits)
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
      | uu____3332 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3352 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3356 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3356
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3363 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3363
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3368 = destruct_comp c1 in
                    match uu____3368 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3381 =
                            let uu____3382 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3383 =
                              let uu____3384 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3385 =
                                let uu____3387 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3388 =
                                  let uu____3390 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3390] in
                                uu____3387 :: uu____3388 in
                              uu____3384 :: uu____3385 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3382
                              uu____3383 in
                          uu____3381 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___133_3395 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___133_3395.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___133_3395.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___133_3395.FStar_Syntax_Syntax.cflags);
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
            let uu____3427 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3427
            then (lc, g0)
            else
              ((let uu____3432 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3432
                then
                  let uu____3433 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3434 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3433 uu____3434
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3441  ->
                          match uu___100_3441 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3443 -> [])) in
                let strengthen uu____3449 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3457 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3457 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3464 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3466 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3466) in
                           if uu____3464
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3473 =
                                 let uu____3474 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3474 in
                               FStar_Syntax_Util.comp_set_flags uu____3473
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3479 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3479
                           then
                             let uu____3480 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3481 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3480 uu____3481
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3484 = destruct_comp c2 in
                           match uu____3484 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3497 =
                                   let uu____3498 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3499 =
                                     let uu____3500 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3501 =
                                       let uu____3503 =
                                         let uu____3504 =
                                           let uu____3505 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3505 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3504 in
                                       let uu____3506 =
                                         let uu____3508 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3508] in
                                       uu____3503 :: uu____3506 in
                                     uu____3500 :: uu____3501 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3498
                                     uu____3499 in
                                 uu____3497 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3514 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3514
                                 then
                                   let uu____3515 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3515
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3518 =
                  let uu___134_3519 = lc in
                  let uu____3520 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3521 =
                    let uu____3523 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3525 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3525) in
                    if uu____3523 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3520;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___134_3519.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3521;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3518,
                  (let uu___135_3529 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___135_3529.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___135_3529.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___135_3529.FStar_TypeChecker_Env.implicits)
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
        let uu____3547 =
          let uu____3550 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3551 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3550, uu____3551) in
        match uu____3547 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3560 =
                let uu____3561 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3562 =
                  let uu____3563 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3564 =
                    let uu____3566 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3566] in
                  uu____3563 :: uu____3564 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3561 uu____3562 in
              uu____3560 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3574 =
                let uu____3575 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3576 =
                  let uu____3577 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3578 =
                    let uu____3580 =
                      let uu____3581 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3581 in
                    let uu____3582 =
                      let uu____3584 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3584] in
                    uu____3580 :: uu____3582 in
                  uu____3577 :: uu____3578 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3575 uu____3576 in
              uu____3574 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3592 =
                let uu____3593 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3594 =
                  let uu____3595 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3596 =
                    let uu____3598 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3599 =
                      let uu____3601 =
                        let uu____3602 =
                          let uu____3603 =
                            let uu____3604 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3604] in
                          FStar_Syntax_Util.abs uu____3603 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3602 in
                      [uu____3601] in
                    uu____3598 :: uu____3599 in
                  uu____3595 :: uu____3596 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3593 uu____3594 in
              uu____3592 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3613 = FStar_TypeChecker_Env.get_range env in
              bind uu____3613 env FStar_Pervasives_Native.None
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
          let comp uu____3635 =
            let uu____3636 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3636
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3639 =
                 let uu____3652 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3653 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3652 uu____3653 in
               match uu____3639 with
               | ((md,uu____3655,uu____3656),(u_res_t,res_t,wp_then),
                  (uu____3660,uu____3661,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3690 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3691 =
                       let uu____3692 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3693 =
                         let uu____3694 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3695 =
                           let uu____3697 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3698 =
                             let uu____3700 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3701 =
                               let uu____3703 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3703] in
                             uu____3700 :: uu____3701 in
                           uu____3697 :: uu____3698 in
                         uu____3694 :: uu____3695 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3692 uu____3693 in
                     uu____3691 FStar_Pervasives_Native.None uu____3690 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3711 =
                     let uu____3712 = FStar_Options.split_cases () in
                     uu____3712 > (Prims.parse_int "0") in
                   if uu____3711
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3718 =
                          let uu____3719 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3720 =
                            let uu____3721 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3722 =
                              let uu____3724 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3724] in
                            uu____3721 :: uu____3722 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3719 uu____3720 in
                        uu____3718 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3729 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3729;
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
      let uu____3738 =
        let uu____3739 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3739 in
      FStar_Syntax_Syntax.fvar uu____3738 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3766  ->
                 match uu____3766 with
                 | (uu____3769,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____3774 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3776 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3776
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3796 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3797 =
                 let uu____3798 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3799 =
                   let uu____3800 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3801 =
                     let uu____3803 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3804 =
                       let uu____3806 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3807 =
                         let uu____3809 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3809] in
                       uu____3806 :: uu____3807 in
                     uu____3803 :: uu____3804 in
                   uu____3800 :: uu____3801 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3798 uu____3799 in
               uu____3797 FStar_Pervasives_Native.None uu____3796 in
             let default_case =
               let post_k =
                 let uu____3818 =
                   let uu____3822 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3822] in
                 let uu____3823 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3818 uu____3823 in
               let kwp =
                 let uu____3829 =
                   let uu____3833 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3833] in
                 let uu____3834 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3829 uu____3834 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____3839 =
                   let uu____3840 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3840] in
                 let uu____3841 =
                   let uu____3842 =
                     let uu____3845 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3845 in
                   let uu____3846 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____3842 uu____3846 in
                 FStar_Syntax_Util.abs uu____3839 uu____3841
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
                 (fun uu____3868  ->
                    fun celse  ->
                      match uu____3868 with
                      | (g,cthen) ->
                          let uu____3874 =
                            let uu____3887 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3887 celse in
                          (match uu____3874 with
                           | ((md,uu____3889,uu____3890),(uu____3891,uu____3892,wp_then),
                              (uu____3894,uu____3895,wp_else)) ->
                               let uu____3906 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3906 []))
                 lcases default_case in
             let uu____3907 =
               let uu____3908 = FStar_Options.split_cases () in
               uu____3908 > (Prims.parse_int "0") in
             if uu____3907
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3912 = destruct_comp comp1 in
                match uu____3912 with
                | (uu____3916,uu____3917,wp) ->
                    let wp1 =
                      let uu____3922 =
                        let uu____3923 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3924 =
                          let uu____3925 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3926 =
                            let uu____3928 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3928] in
                          uu____3925 :: uu____3926 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3923 uu____3924 in
                      uu____3922 FStar_Pervasives_Native.None
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
          let uu____3947 =
            ((let uu____3950 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____3950) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3952 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____3952) in
          if uu____3947
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____3960 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3964 =
            (let uu____3967 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____3967) || env.FStar_TypeChecker_Env.lax in
          if uu____3964
          then c
          else
            (let uu____3971 = FStar_Syntax_Util.is_partial_return c in
             if uu____3971
             then c
             else
               (let uu____3975 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____3975
                then
                  let uu____3978 =
                    let uu____3979 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____3979 in
                  (if uu____3978
                   then
                     let uu____3982 =
                       let uu____3983 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____3984 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____3983 uu____3984 in
                     failwith uu____3982
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____3989 =
                        let uu____3990 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____3990 in
                      if uu____3989
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___136_3995 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___136_3995.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___136_3995.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___136_3995.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4006 =
                       let uu____4009 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4009
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4006 in
                   let eq1 =
                     let uu____4013 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4013 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4015 =
                     let uu____4016 =
                       let uu____4021 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____4021.FStar_Syntax_Syntax.comp in
                     uu____4016 () in
                   FStar_Syntax_Util.comp_set_flags uu____4015 flags))) in
        let uu___137_4023 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4023.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4023.FStar_Syntax_Syntax.res_typ);
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
          let uu____4046 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4046 with
          | FStar_Pervasives_Native.None  ->
              let uu____4051 =
                let uu____4052 =
                  let uu____4055 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4056 = FStar_TypeChecker_Env.get_range env in
                  (uu____4055, uu____4056) in
                FStar_Errors.Error uu____4052 in
              raise uu____4051
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
            let uu____4086 =
              let uu____4087 = FStar_Syntax_Subst.compress t2 in
              uu____4087.FStar_Syntax_Syntax.n in
            match uu____4086 with
            | FStar_Syntax_Syntax.Tm_type uu____4090 -> true
            | uu____4091 -> false in
          let uu____4092 =
            let uu____4093 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4093.FStar_Syntax_Syntax.n in
          match uu____4092 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4099 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____4106 =
                  let uu____4107 =
                    let uu____4108 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4108 in
                  (FStar_Pervasives_Native.None, uu____4107) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____4106 in
              let e1 =
                let uu____4117 =
                  let uu____4118 =
                    let uu____4119 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4119] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4118 in
                uu____4117
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4126 -> (e, lc)
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
              (let uu____4153 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4153 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4166 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4178 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4178, false)
            else
              (let uu____4182 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4182, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____4188) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___138_4192 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___138_4192.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___138_4192.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___138_4192.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____4196 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4196 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___139_4201 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_4201.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_4201.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___139_4201.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___140_4204 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___140_4204.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___140_4204.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___140_4204.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4210 =
                     let uu____4211 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4211
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____4216 =
                          let uu____4217 = FStar_Syntax_Subst.compress f1 in
                          uu____4217.FStar_Syntax_Syntax.n in
                        match uu____4216 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4222,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4224;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4225;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4226;_},uu____4227)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___141_4241 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___141_4241.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___141_4241.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___141_4241.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4242 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4247 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4247
                              then
                                let uu____4248 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4249 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4250 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4251 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4248 uu____4249 uu____4250 uu____4251
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4254 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____4254 with
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
                                  let uu____4265 = destruct_comp ct in
                                  (match uu____4265 with
                                   | (u_t,uu____4272,uu____4273) ->
                                       let wp =
                                         let uu____4277 =
                                           let uu____4278 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4279 =
                                             let uu____4280 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4281 =
                                               let uu____4283 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4283] in
                                             uu____4280 :: uu____4281 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4278 uu____4279 in
                                         uu____4277
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4289 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4289 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4299 =
                                             let uu____4300 =
                                               let uu____4301 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4301] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4300 in
                                           uu____4299
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4307 =
                                         let uu____4310 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4321 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4322 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4310
                                           uu____4321 e cret uu____4322 in
                                       (match uu____4307 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___142_4328 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___142_4328.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___142_4328.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4330 =
                                                let uu____4331 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4331 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____4330
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4341 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4341
                                              then
                                                let uu____4342 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4342
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4349  ->
                             match uu___101_4349 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4351 -> [])) in
                   let lc1 =
                     let uu___143_4353 = lc in
                     let uu____4354 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4354;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___144_4356 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_4356.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_4356.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_4356.FStar_TypeChecker_Env.implicits)
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
        let uu____4378 =
          let uu____4379 =
            let uu____4380 =
              let uu____4381 =
                let uu____4382 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4382 in
              [uu____4381] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4380 in
          uu____4379 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4378 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4391 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4391
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4402 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4411 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4428)::(ens,uu____4430)::uu____4431 ->
                    let uu____4453 =
                      let uu____4455 = norm req in
                      FStar_Pervasives_Native.Some uu____4455 in
                    let uu____4456 =
                      let uu____4457 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4457 in
                    (uu____4453, uu____4456)
                | uu____4459 ->
                    let uu____4465 =
                      let uu____4466 =
                        let uu____4469 =
                          let uu____4470 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4470 in
                        (uu____4469, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4466 in
                    raise uu____4465)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4480)::uu____4481 ->
                    let uu____4495 =
                      let uu____4498 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____4498 in
                    (match uu____4495 with
                     | (us_r,uu____4515) ->
                         let uu____4516 =
                           let uu____4519 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____4519 in
                         (match uu____4516 with
                          | (us_e,uu____4536) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4539 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4539
                                  us_r in
                              let as_ens =
                                let uu____4541 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4541
                                  us_e in
                              let req =
                                let uu____4545 =
                                  let uu____4546 =
                                    let uu____4547 =
                                      let uu____4554 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4554] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4547 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4546 in
                                uu____4545
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4570 =
                                  let uu____4571 =
                                    let uu____4572 =
                                      let uu____4579 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4579] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4572 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4571 in
                                uu____4570 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4592 =
                                let uu____4594 = norm req in
                                FStar_Pervasives_Native.Some uu____4594 in
                              let uu____4595 =
                                let uu____4596 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4596 in
                              (uu____4592, uu____4595)))
                | uu____4598 -> failwith "Impossible"))
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
      (let uu____4620 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4620
       then
         let uu____4621 = FStar_Syntax_Print.term_to_string tm in
         let uu____4622 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4621 uu____4622
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
        (let uu____4646 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4646
         then
           let uu____4647 = FStar_Syntax_Print.term_to_string tm in
           let uu____4648 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4647
             uu____4648
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4654 =
      let uu____4655 =
        let uu____4656 = FStar_Syntax_Subst.compress t in
        uu____4656.FStar_Syntax_Syntax.n in
      match uu____4655 with
      | FStar_Syntax_Syntax.Tm_app uu____4659 -> false
      | uu____4669 -> true in
    if uu____4654
    then t
    else
      (let uu____4671 = FStar_Syntax_Util.head_and_args t in
       match uu____4671 with
       | (head1,args) ->
           let uu____4697 =
             let uu____4698 =
               let uu____4699 = FStar_Syntax_Subst.compress head1 in
               uu____4699.FStar_Syntax_Syntax.n in
             match uu____4698 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4702 -> false in
           if uu____4697
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____4718 ->
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
             let uu____4749 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4749 with
             | (formals,uu____4758) ->
                 let n_implicits =
                   let uu____4770 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4810  ->
                             match uu____4810 with
                             | (uu____4814,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____4770 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4889 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4889 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4910 =
                     let uu____4911 =
                       let uu____4914 =
                         let uu____4915 = FStar_Util.string_of_int n_expected in
                         let uu____4922 = FStar_Syntax_Print.term_to_string e in
                         let uu____4923 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4915 uu____4922 uu____4923 in
                       let uu____4930 = FStar_TypeChecker_Env.get_range env in
                       (uu____4914, uu____4930) in
                     FStar_Errors.Error uu____4911 in
                   raise uu____4910
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___102_4948 =
             match uu___102_4948 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4967 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4967 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____5028) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5050,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5069 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5069 with
                           | (v1,uu____5090,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5100 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5100 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5149 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5149)))
                      | (uu____5163,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5187 =
                      let uu____5201 = inst_n_binders t in
                      aux [] uu____5201 bs1 in
                    (match uu____5187 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5239) -> (e, torig, guard)
                          | (uu____5255,[]) when
                              let uu____5271 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5271 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5272 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5291 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5304 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5311 =
      let uu____5313 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5313
        (FStar_List.map
           (fun u  ->
              let uu____5320 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5320 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5311 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5334 = FStar_Util.set_is_empty x in
      if uu____5334
      then []
      else
        (let s =
           let uu____5339 =
             let uu____5341 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5341 in
           FStar_All.pipe_right uu____5339 FStar_Util.set_elements in
         (let uu____5346 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5346
          then
            let uu____5347 =
              let uu____5348 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5348 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5347
          else ());
         (let r =
            let uu____5353 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____5353 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5365 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5365
                     then
                       let uu____5366 =
                         let uu____5367 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5367 in
                       let uu____5368 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5369 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5366 uu____5368 uu____5369
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
        let uu____5388 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5388 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_5418 =
  match uu___103_5418 with
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
        | ([],uu____5461) -> generalized_univ_names
        | (uu____5465,[]) -> explicit_univ_names
        | uu____5469 ->
            let uu____5474 =
              let uu____5475 =
                let uu____5478 =
                  let uu____5479 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5479 in
                (uu____5478, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5475 in
            raise uu____5474
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
      (let uu____5495 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5495
       then
         let uu____5496 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5496
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5501 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5501
        then
          let uu____5502 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5502
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____5508 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5508))
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
      let uu____5540 =
        let uu____5541 =
          FStar_Util.for_all
            (fun uu____5549  ->
               match uu____5549 with
               | (uu____5554,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5541 in
      if uu____5540
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____5577 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5577
            then
              let uu____5578 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5578
            else ());
           (let c1 =
              let uu____5581 = FStar_TypeChecker_Env.should_verify env in
              if uu____5581
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
            (let uu____5584 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5584
             then
               let uu____5585 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5585
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5625 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5625 FStar_Util.set_elements in
         let uu____5679 =
           let uu____5699 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5772  ->
                     match uu____5772 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____5814 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____5814
                           then
                             let uu____5815 =
                               let uu____5816 =
                                 let uu____5818 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____5818
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____5816
                                 (FStar_String.concat ", ") in
                             let uu____5833 =
                               let uu____5834 =
                                 let uu____5836 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____5836
                                   (FStar_List.map
                                      (fun uu____5853  ->
                                         match uu____5853 with
                                         | (u,t2) ->
                                             let uu____5858 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____5859 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____5858 uu____5859)) in
                               FStar_All.pipe_right uu____5834
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____5815 uu____5833
                           else ());
                          (let univs2 =
                             let uu____5864 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____5879  ->
                                    match uu____5879 with
                                    | (uu____5884,t2) ->
                                        let uu____5886 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____5886) univs1 uu____5864 in
                           let uvs = gen_uvars uvt in
                           (let uu____5901 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____5901
                            then
                              let uu____5902 =
                                let uu____5903 =
                                  let uu____5905 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____5905
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____5903
                                  (FStar_String.concat ", ") in
                              let uu____5920 =
                                let uu____5921 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____5942  ->
                                          match uu____5942 with
                                          | (u,t2) ->
                                              let uu____5947 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____5948 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____5947 uu____5948)) in
                                FStar_All.pipe_right uu____5921
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____5902 uu____5920
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____5699 FStar_List.unzip in
         match uu____5679 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____6073 = FStar_List.hd univs1 in
               let uu____6076 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____6089 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____6089
                      then out
                      else
                        (let uu____6092 =
                           let uu____6093 =
                             let uu____6096 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____6096) in
                           FStar_Errors.Error uu____6093 in
                         raise uu____6092)) uu____6073 uu____6076 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6101 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6101
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
                      (fun uu____6150  ->
                         match uu____6150 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6195  ->
                                       match uu____6195 with
                                       | (u,k) ->
                                           let uu____6203 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6203 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6209;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6210;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6211;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6217,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6219;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6220;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6221;_},uu____6222);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6223;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6224;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6225;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____6243 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6247 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____6250 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6250 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6274 =
                                                         let uu____6276 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____6276 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6274 kres in
                                                     let t =
                                                       let uu____6279 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6279
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6282 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____6300 ->
                                   let uu____6308 = (e, c) in
                                   (match uu____6308 with
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
                                          let uu____6320 =
                                            let uu____6321 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6321.FStar_Syntax_Syntax.n in
                                          match uu____6320 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6338 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6338 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6348 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____6350 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6350)) in
                             (match uu____6282 with
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
      (let uu____6390 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6390
       then
         let uu____6391 =
           let uu____6392 =
             FStar_List.map
               (fun uu____6401  ->
                  match uu____6401 with
                  | (lb,uu____6406,uu____6407) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6392 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6391
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6421  ->
              match uu____6421 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6436 =
           let uu____6443 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6463  ->
                     match uu____6463 with | (uu____6469,e,c) -> (e, c))) in
           gen env uu____6443 in
         match uu____6436 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6505  ->
                     match uu____6505 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____6558  ->
                  fun uu____6559  ->
                    match (uu____6558, uu____6559) with
                    | ((l,uu____6592,uu____6593),(us,e,c)) ->
                        ((let uu____6619 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6619
                          then
                            let uu____6620 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6621 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6622 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6623 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6620 uu____6621 uu____6622 uu____6623
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6649  ->
              match uu____6649 with
              | (l,generalized_univs,t,c) ->
                  let uu____6667 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6667, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6704 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6704 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____6708 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____6708) in
          let is_var e1 =
            let uu____6714 =
              let uu____6715 = FStar_Syntax_Subst.compress e1 in
              uu____6715.FStar_Syntax_Syntax.n in
            match uu____6714 with
            | FStar_Syntax_Syntax.Tm_name uu____6718 -> true
            | uu____6719 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___145_6739 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_6739.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_6739.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6740 ->
                let uu___146_6741 = e2 in
                let uu____6742 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___146_6741.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6742;
                  FStar_Syntax_Syntax.pos =
                    (uu___146_6741.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___146_6741.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___147_6751 = env1 in
            let uu____6752 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___147_6751.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___147_6751.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___147_6751.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___147_6751.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___147_6751.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___147_6751.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___147_6751.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___147_6751.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___147_6751.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___147_6751.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___147_6751.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___147_6751.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___147_6751.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___147_6751.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___147_6751.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6752;
              FStar_TypeChecker_Env.is_iface =
                (uu___147_6751.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___147_6751.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___147_6751.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___147_6751.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___147_6751.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___147_6751.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___147_6751.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___147_6751.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___147_6751.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___147_6751.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___147_6751.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6753 = check env2 t1 t2 in
          match uu____6753 with
          | FStar_Pervasives_Native.None  ->
              let uu____6757 =
                let uu____6758 =
                  let uu____6761 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6762 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6761, uu____6762) in
                FStar_Errors.Error uu____6758 in
              raise uu____6757
          | FStar_Pervasives_Native.Some g ->
              ((let uu____6767 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6767
                then
                  let uu____6768 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6768
                else ());
               (let uu____6770 = decorate e t2 in (uu____6770, g)))
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
        let uu____6797 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6797
        then
          let uu____6800 = discharge g1 in
          let uu____6801 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6800, uu____6801)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6813 =
               let uu____6814 =
                 let uu____6815 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6815 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6814
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6813
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6817 = destruct_comp c1 in
           match uu____6817 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6829 = FStar_TypeChecker_Env.get_range env in
                 let uu____6830 =
                   let uu____6831 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6832 =
                     let uu____6833 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6834 =
                       let uu____6836 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6836] in
                     uu____6833 :: uu____6834 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6831 uu____6832 in
                 uu____6830
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6829 in
               ((let uu____6842 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6842
                 then
                   let uu____6843 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6843
                 else ());
                (let g2 =
                   let uu____6846 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6846 in
                 let uu____6847 = discharge g2 in
                 let uu____6848 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6847, uu____6848))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6874 =
        match uu___104_6874 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6880)::[] -> f fst1
        | uu____6893 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6898 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6898
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6907 =
          let uu____6910 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6910 in
        FStar_All.pipe_right uu____6907
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6921 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6921
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_6935 =
        match uu___105_6935 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6941)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6956)::[] ->
            let uu____6977 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6977
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6982 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6989 =
          let uu____6994 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____6994) in
        let uu____6999 =
          let uu____7005 =
            let uu____7010 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____7010) in
          let uu____7015 =
            let uu____7021 =
              let uu____7026 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____7026) in
            let uu____7031 =
              let uu____7037 =
                let uu____7042 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____7042) in
              let uu____7047 =
                let uu____7053 =
                  let uu____7058 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____7058) in
                [uu____7053; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____7037 :: uu____7047 in
            uu____7021 :: uu____7031 in
          uu____7005 :: uu____7015 in
        uu____6989 :: uu____6999 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7095 =
            FStar_Util.find_map table
              (fun uu____7105  ->
                 match uu____7105 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____7118 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____7118
                     else FStar_Pervasives_Native.None) in
          (match uu____7095 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____7121 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7126 =
      let uu____7127 = FStar_Syntax_Util.un_uinst l in
      uu____7127.FStar_Syntax_Syntax.n in
    match uu____7126 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____7131 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7151)::uu____7152 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7158 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7162,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____7163))::uu____7164 -> bs
      | uu____7173 ->
          let uu____7174 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7174 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____7177 =
                 let uu____7178 = FStar_Syntax_Subst.compress t in
                 uu____7178.FStar_Syntax_Syntax.n in
               (match uu____7177 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7182) ->
                    let uu____7193 =
                      FStar_Util.prefix_until
                        (fun uu___106_7215  ->
                           match uu___106_7215 with
                           | (uu____7219,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7220)) ->
                               false
                           | uu____7222 -> true) bs' in
                    (match uu____7193 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____7240,uu____7241) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____7278,uu____7279) ->
                         let uu____7316 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7327  ->
                                   match uu____7327 with
                                   | (x,uu____7332) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7316
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7359  ->
                                     match uu____7359 with
                                     | (x,i) ->
                                         let uu____7370 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7370, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7376 -> bs))
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
              (let uu____7400 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7400 e.FStar_Syntax_Syntax.pos)
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
          let uu____7426 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____7426
          then e
          else
            (let uu____7428 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7428
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
        (let uu____7458 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7458
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7460 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7460))
         else ());
        (let fv =
           let uu____7463 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7463
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
         let uu____7469 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___148_7479 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___148_7479.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___148_7479.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___148_7479.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___148_7479.FStar_Syntax_Syntax.sigattrs)
           }), uu____7469))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7491 =
        match uu___107_7491 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7492 -> false in
      let reducibility uu___108_7496 =
        match uu___108_7496 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7497 -> false in
      let assumption uu___109_7501 =
        match uu___109_7501 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7502 -> false in
      let reification uu___110_7506 =
        match uu___110_7506 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7507 -> true
        | uu____7508 -> false in
      let inferred uu___111_7512 =
        match uu___111_7512 with
        | FStar_Syntax_Syntax.Discriminator uu____7513 -> true
        | FStar_Syntax_Syntax.Projector uu____7514 -> true
        | FStar_Syntax_Syntax.RecordType uu____7517 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7522 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7527 -> false in
      let has_eq uu___112_7531 =
        match uu___112_7531 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7532 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7578 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7582 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7585 =
        let uu____7586 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7589  ->
                  match uu___113_7589 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7590 -> false)) in
        FStar_All.pipe_right uu____7586 Prims.op_Negation in
      if uu____7585
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7602 =
            let uu____7603 =
              let uu____7606 =
                let uu____7607 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7607 msg in
              (uu____7606, r) in
            FStar_Errors.Error uu____7603 in
          raise uu____7602 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7615 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7627 =
            let uu____7628 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7628 in
          if uu____7627 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____7632),uu____7633) ->
              ((let uu____7642 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7642
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7645 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7645
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7650 ->
              let uu____7655 =
                let uu____7656 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7656 in
              if uu____7655 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7661 ->
              let uu____7665 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7665 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7668 ->
              let uu____7672 =
                let uu____7673 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7673 in
              if uu____7672 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7678 ->
              let uu____7679 =
                let uu____7680 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7680 in
              if uu____7679 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7685 ->
              let uu____7686 =
                let uu____7687 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7687 in
              if uu____7686 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7692 ->
              let uu____7699 =
                let uu____7700 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7700 in
              if uu____7699 then err'1 () else ()
          | uu____7705 -> ()))
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
                          let uu____7772 =
                            let uu____7775 =
                              let uu____7776 =
                                let uu____7781 =
                                  let uu____7782 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7782 in
                                (uu____7781, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7776 in
                            FStar_Syntax_Syntax.mk uu____7775 in
                          uu____7772 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7812  ->
                                  match uu____7812 with
                                  | (x,imp) ->
                                      let uu____7819 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7819, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7823 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7823 in
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
                             let uu____7832 =
                               let uu____7833 =
                                 let uu____7834 =
                                   let uu____7835 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7836 =
                                     let uu____7837 =
                                       let uu____7838 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7838 in
                                     [uu____7837] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7835
                                     uu____7836 in
                                 uu____7834 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7833 in
                             FStar_Syntax_Util.refine x uu____7832 in
                           let uu____7843 =
                             let uu___149_7844 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___149_7844.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___149_7844.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7843) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7855 =
                          FStar_List.map
                            (fun uu____7868  ->
                               match uu____7868 with
                               | (x,uu____7875) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7855 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7902  ->
                                match uu____7902 with
                                | (x,uu____7909) ->
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
                             (let uu____7920 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____7920)
                               ||
                               (let uu____7922 =
                                  let uu____7923 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7923.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7922) in
                           let quals =
                             let uu____7926 =
                               let uu____7928 =
                                 let uu____7930 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7930
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7933 =
                                 FStar_List.filter
                                   (fun uu___114_7936  ->
                                      match uu___114_7936 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7937 -> false) iquals in
                               FStar_List.append uu____7928 uu____7933 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7926 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7950 =
                                 let uu____7951 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7951 in
                               FStar_Syntax_Syntax.mk_Total uu____7950 in
                             let uu____7952 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7952 in
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
                           (let uu____7955 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7955
                            then
                              let uu____7956 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7956
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
                                             fun uu____7991  ->
                                               match uu____7991 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____8007 =
                                                       let uu____8009 =
                                                         let uu____8010 =
                                                           let uu____8015 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____8015,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8010 in
                                                       pos uu____8009 in
                                                     (uu____8007, b)
                                                   else
                                                     (let uu____8018 =
                                                        let uu____8020 =
                                                          let uu____8021 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8021 in
                                                        pos uu____8020 in
                                                      (uu____8018, b)))) in
                                   let pat_true =
                                     let uu____8033 =
                                       let uu____8035 =
                                         let uu____8036 =
                                           let uu____8043 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____8043, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8036 in
                                       pos uu____8035 in
                                     (uu____8033,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____8066 =
                                       let uu____8068 =
                                         let uu____8069 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8069 in
                                       pos uu____8068 in
                                     (uu____8066,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____8079 =
                                     let uu____8082 =
                                       let uu____8083 =
                                         let uu____8098 =
                                           let uu____8100 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8101 =
                                             let uu____8103 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8103] in
                                           uu____8100 :: uu____8101 in
                                         (arg_exp, uu____8098) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8083 in
                                     FStar_Syntax_Syntax.mk uu____8082 in
                                   uu____8079 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____8114 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8114
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
                                let uu____8121 =
                                  let uu____8124 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____8124 in
                                let uu____8125 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____8121;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____8125
                                } in
                              let impl =
                                let uu____8129 =
                                  let uu____8130 =
                                    let uu____8134 =
                                      let uu____8136 =
                                        let uu____8137 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8137
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8136] in
                                    ((false, [lb]), uu____8134) in
                                  FStar_Syntax_Syntax.Sig_let uu____8130 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8129;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____8148 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8148
                               then
                                 let uu____8149 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8149
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
                                fun uu____8178  ->
                                  match uu____8178 with
                                  | (a,uu____8182) ->
                                      let uu____8183 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8183 with
                                       | (field_name,uu____8187) ->
                                           let field_proj_tm =
                                             let uu____8189 =
                                               let uu____8190 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8190 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8189 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8204 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8228  ->
                                    match uu____8228 with
                                    | (x,uu____8233) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8235 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8235 with
                                         | (field_name,uu____8240) ->
                                             let t =
                                               let uu____8242 =
                                                 let uu____8243 =
                                                   let uu____8246 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8246 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8243 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8242 in
                                             let only_decl =
                                               (let uu____8250 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____8250)
                                                 ||
                                                 (let uu____8252 =
                                                    let uu____8253 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8253.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8252) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8263 =
                                                   FStar_List.filter
                                                     (fun uu___115_8266  ->
                                                        match uu___115_8266
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8267 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8263
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_8276  ->
                                                         match uu___116_8276
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8277 ->
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
                                             ((let uu____8280 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8280
                                               then
                                                 let uu____8281 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8281
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
                                                           fun uu____8311  ->
                                                             match uu____8311
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8327
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8327,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8338
                                                                    =
                                                                    let uu____8340
                                                                    =
                                                                    let uu____8341
                                                                    =
                                                                    let uu____8346
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8346,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8341 in
                                                                    pos
                                                                    uu____8340 in
                                                                    (uu____8338,
                                                                    b))
                                                                   else
                                                                    (let uu____8349
                                                                    =
                                                                    let uu____8351
                                                                    =
                                                                    let uu____8352
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8352 in
                                                                    pos
                                                                    uu____8351 in
                                                                    (uu____8349,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8362 =
                                                     let uu____8364 =
                                                       let uu____8365 =
                                                         let uu____8372 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8372,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8365 in
                                                     pos uu____8364 in
                                                   let uu____8377 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8362,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8377) in
                                                 let body =
                                                   let uu____8387 =
                                                     let uu____8390 =
                                                       let uu____8391 =
                                                         let uu____8406 =
                                                           let uu____8408 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8408] in
                                                         (arg_exp,
                                                           uu____8406) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8391 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8390 in
                                                   uu____8387
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8420 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8420
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
                                                   let uu____8426 =
                                                     let uu____8429 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8429 in
                                                   let uu____8430 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8426;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8430
                                                   } in
                                                 let impl =
                                                   let uu____8434 =
                                                     let uu____8435 =
                                                       let uu____8439 =
                                                         let uu____8441 =
                                                           let uu____8442 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8442
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8441] in
                                                       ((false, [lb]),
                                                         uu____8439) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8435 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8434;
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
                                                 (let uu____8453 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8453
                                                  then
                                                    let uu____8454 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8454
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8204 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8488) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____8491 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8491 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8504 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8504 with
                    | (formals,uu____8514) ->
                        let uu____8525 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8547 =
                                   let uu____8548 =
                                     let uu____8549 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8549 in
                                   FStar_Ident.lid_equals typ_lid uu____8548 in
                                 if uu____8547
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8559,uvs',tps,typ0,uu____8563,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8580 -> failwith "Impossible"
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
                        (match uu____8525 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8622 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8622 with
                              | (indices,uu____8632) ->
                                  let refine_domain =
                                    let uu____8644 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_8648  ->
                                              match uu___117_8648 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8649 -> true
                                              | uu____8654 -> false)) in
                                    if uu____8644
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_8661 =
                                      match uu___118_8661 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8663,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8670 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8671 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8671 with
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
                                    let uu____8679 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8679 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8717  ->
                                               fun uu____8718  ->
                                                 match (uu____8717,
                                                         uu____8718)
                                                 with
                                                 | ((x,uu____8728),(x',uu____8730))
                                                     ->
                                                     let uu____8735 =
                                                       let uu____8740 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8740) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8735) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8741 -> []