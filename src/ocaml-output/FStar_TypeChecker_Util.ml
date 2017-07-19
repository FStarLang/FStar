open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____17 = FStar_TypeChecker_Env.get_range env in
      let uu____18 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____17 uu____18
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____22 =
      let uu____23 = FStar_Syntax_Subst.compress t in
      uu____23.FStar_Syntax_Syntax.n in
    match uu____22 with
    | FStar_Syntax_Syntax.Tm_type uu____28 -> true
    | uu____29 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____39 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____39
      (FStar_List.filter
         (fun uu____50  ->
            match uu____50 with
            | (x,uu____56) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____68 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____69 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____69) in
        if uu____68
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____71 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____71 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____78 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____78
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___97_85  ->
    match uu___97_85 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____87);
        FStar_Syntax_Syntax.tk = uu____88;
        FStar_Syntax_Syntax.pos = uu____89;
        FStar_Syntax_Syntax.vars = uu____90;_} -> uv
    | uu____119 -> failwith "Impossible"
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
          let uu____144 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____144 with
          | FStar_Pervasives_Native.Some (uu____169::(tm,uu____171)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____241 ->
              let uu____254 = new_uvar_aux env k in
              (match uu____254 with
               | (t,u) ->
                   let g =
                     let uu___117_274 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____275 =
                       let uu____290 =
                         let uu____303 = as_uvar u in
                         (reason, env, uu____303, t, k, r) in
                       [uu____290] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___117_274.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___117_274.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___117_274.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____275
                     } in
                   let uu____328 =
                     let uu____335 =
                       let uu____340 = as_uvar u in (uu____340, r) in
                     [uu____335] in
                   (t, uu____328, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____368 =
        let uu____369 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____369 in
      if uu____368
      then
        let us =
          let uu____375 =
            let uu____378 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____409  ->
                 match uu____409 with
                 | (x,uu____423) -> FStar_Syntax_Print.uvar_to_string x)
              uu____378 in
          FStar_All.pipe_right uu____375 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____452 =
            let uu____453 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____453 in
          FStar_Errors.err r uu____452);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____466 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____466 with
    | FStar_Pervasives_Native.None  ->
        let uu____471 =
          let uu____472 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____473 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____472 uu____473 in
        failwith uu____471
    | FStar_Pervasives_Native.Some tk -> tk
let force_sort s =
  let uu____494 =
    let uu____499 = force_sort' s in FStar_Syntax_Syntax.mk uu____499 in
  uu____494 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____515  ->
      match uu____515 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____525;
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
                   let uu____575 =
                     let uu____576 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____576.FStar_Syntax_Syntax.n in
                   match uu____575 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____585 = FStar_Syntax_Util.type_u () in
                       (match uu____585 with
                        | (k,uu____595) ->
                            let t2 =
                              let uu____597 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____597
                                FStar_Pervasives_Native.fst in
                            ((let uu___118_606 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_606.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_606.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____607 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____644) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____655) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____744) ->
                       let uu____789 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____836  ->
                                 fun uu____837  ->
                                   match (uu____836, uu____837) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____915 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____915 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____789 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____1027 = aux must_check_ty1 scope body in
                            (match uu____1027 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____1056 =
                                         FStar_Options.ml_ish () in
                                       if uu____1056
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____1065 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____1065
                                   then
                                     let uu____1066 =
                                       FStar_Range.string_of_range r in
                                     let uu____1067 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____1068 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____1066 uu____1067 uu____1068
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____1082 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____1096 =
                            let uu____1101 =
                              let uu____1102 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____1102
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____1101 in
                          (uu____1096, false)) in
                 let uu____1115 =
                   let uu____1124 = t_binders env in aux false uu____1124 e in
                 match uu____1115 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1153 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____1153
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1159 =
                                let uu____1160 =
                                  let uu____1165 =
                                    let uu____1166 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____1166 in
                                  (uu____1165, rng) in
                                FStar_Errors.Error uu____1160 in
                              raise uu____1159)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1178 ->
               let uu____1179 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1179 with
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
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1300) ->
              let uu____1309 = FStar_Syntax_Util.type_u () in
              (match uu____1309 with
               | (k,uu____1333) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_1336 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_1336.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_1336.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____1337 =
                     let uu____1342 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____1342 t in
                   (match uu____1337 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_1368 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___120_1368.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___120_1368.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1380 = FStar_Syntax_Util.type_u () in
              (match uu____1380 with
               | (t,uu____1404) ->
                   let x1 =
                     let uu___121_1406 = x in
                     let uu____1407 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_1406.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_1406.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1407
                     } in
                   let env2 =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env1 x1
                     else env1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [], [x1], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1430 = FStar_Syntax_Util.type_u () in
              (match uu____1430 with
               | (t,uu____1454) ->
                   let x1 =
                     let uu___122_1456 = x in
                     let uu____1457 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_1456.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_1456.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1457
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1500 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1611  ->
                        fun uu____1612  ->
                          match (uu____1611, uu____1612) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1801 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1801 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____1500 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____2001 =
                       let uu____2006 =
                         let uu____2007 =
                           let uu____2016 =
                             let uu____2021 =
                               let uu____2022 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____2023 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2022
                                 uu____2023 in
                             uu____2021 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____2016,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____2007 in
                       FStar_Syntax_Syntax.mk uu____2006 in
                     uu____2001 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____2038 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____2049 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____2060 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____2038, uu____2049, uu____2060, env2, e,
                     (let uu___123_2085 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___123_2085.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___123_2085.FStar_Syntax_Syntax.p)
                      }))) in
        let rec elaborate_pat env1 p1 =
          let maybe_dot inaccessible a r =
            if allow_implicits && inaccessible
            then
              FStar_Syntax_Syntax.withinfo
                (FStar_Syntax_Syntax.Pat_dot_term
                   (a, FStar_Syntax_Syntax.tun))
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
            else
              FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats1 =
                FStar_List.map
                  (fun uu____2187  ->
                     match uu____2187 with
                     | (p2,imp) ->
                         let uu____2214 = elaborate_pat env1 p2 in
                         (uu____2214, imp)) pats in
              let uu____2223 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____2223 with
               | (uu____2236,t) ->
                   let uu____2238 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____2238 with
                    | (f,uu____2258) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____2400::uu____2401) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____2466::uu____2467,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____2546  ->
                                      match uu____2546 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____2577 =
                                                   let uu____2580 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____2580 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____2577
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____2586 =
                                                 maybe_dot inaccessible a r in
                                               (uu____2586, true)
                                           | uu____2595 ->
                                               let uu____2598 =
                                                 let uu____2599 =
                                                   let uu____2604 =
                                                     let uu____2605 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2605 in
                                                   (uu____2604,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____2599 in
                                               raise uu____2598)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____2697,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____2698))
                                   when p_imp ->
                                   let uu____2701 = aux formals' pats' in
                                   (p2, true) :: uu____2701
                               | (uu____2724,FStar_Pervasives_Native.Some
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
                                   let uu____2738 = aux formals' pats2 in
                                   (p3, true) :: uu____2738
                               | (uu____2761,imp) ->
                                   let uu____2767 =
                                     let uu____2776 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____2776) in
                                   let uu____2781 = aux formals' pats' in
                                   uu____2767 :: uu____2781) in
                        let uu___124_2800 = p1 in
                        let uu____2805 =
                          let uu____2806 =
                            let uu____2821 = aux f pats1 in (fv, uu____2821) in
                          FStar_Syntax_Syntax.Pat_cons uu____2806 in
                        {
                          FStar_Syntax_Syntax.v = uu____2805;
                          FStar_Syntax_Syntax.ty =
                            (uu___124_2800.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___124_2800.FStar_Syntax_Syntax.p)
                        }))
          | uu____2842 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____2882 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____2882 with
          | (b,a,w,env2,arg,p3) ->
              let uu____2935 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____2935 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____2959 =
                     let uu____2960 =
                       let uu____2965 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____2965, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____2960 in
                   raise uu____2959
               | uu____2982 -> (b, a, w, arg, p3)) in
        let uu____2991 = one_pat true env p in
        match uu____2991 with
        | (b,uu____3017,uu____3018,tm,p1) -> (b, tm, p1)
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
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p in
          let e1 = FStar_Syntax_Util.unmeta e in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____3072,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3074)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____3083,FStar_Syntax_Syntax.Tm_constant uu____3084) ->
              let uu____3085 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____3085
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3089 =
                    let uu____3090 = FStar_Syntax_Print.bv_to_string x in
                    let uu____3091 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3090 uu____3091 in
                  failwith uu____3089)
               else ();
               (let uu____3094 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____3094
                then
                  let uu____3095 = FStar_Syntax_Print.bv_to_string x in
                  let uu____3096 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3095
                    uu____3096
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_3100 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_3100.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_3100.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3104 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____3104
                then
                  let uu____3105 =
                    let uu____3106 = FStar_Syntax_Print.bv_to_string x in
                    let uu____3107 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3106 uu____3107 in
                  failwith uu____3105
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_3111 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_3111.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_3111.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3113),uu____3114) ->
              let s = force_sort e1 in
              let x1 =
                let uu___127_3129 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___127_3129.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___127_3129.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3151 =
                  let uu____3152 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____3152 in
                if uu____3151
                then
                  let uu____3153 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3153
                else ());
               (let uu____3163 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____3163))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____3185;
                FStar_Syntax_Syntax.pos = uu____3186;
                FStar_Syntax_Syntax.vars = uu____3187;_},args))
              ->
              ((let uu____3238 =
                  let uu____3239 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3239 Prims.op_Negation in
                if uu____3238
                then
                  let uu____3240 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3240
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____3395 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____3395
                  | (arg::args2,(argpat,uu____3417)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3514) ->
                           let x =
                             let uu____3544 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____3544 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3568) ->
                           let pat =
                             let uu____3596 = aux argpat e2 in
                             let uu____3597 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3596, uu____3597) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3602 ->
                      let uu____3629 =
                        let uu____3630 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3631 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3630 uu____3631 in
                      failwith uu____3629 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____3647;
                     FStar_Syntax_Syntax.pos = uu____3648;
                     FStar_Syntax_Syntax.vars = uu____3649;_},uu____3650);
                FStar_Syntax_Syntax.tk = uu____3651;
                FStar_Syntax_Syntax.pos = uu____3652;
                FStar_Syntax_Syntax.vars = uu____3653;_},args))
              ->
              ((let uu____3712 =
                  let uu____3713 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3713 Prims.op_Negation in
                if uu____3712
                then
                  let uu____3714 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3714
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____3869 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____3869
                  | (arg::args2,(argpat,uu____3891)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3988) ->
                           let x =
                             let uu____4018 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____4018 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____4042) ->
                           let pat =
                             let uu____4070 = aux argpat e2 in
                             let uu____4071 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____4070, uu____4071) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____4076 ->
                      let uu____4103 =
                        let uu____4104 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____4105 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____4104 uu____4105 in
                      failwith uu____4103 in
                match_args [] args argpats))
          | uu____4118 ->
              let uu____4123 =
                let uu____4124 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____4125 = FStar_Syntax_Print.pat_to_string qq in
                let uu____4126 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____4124 uu____4125 uu____4126 in
              failwith uu____4123 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun pat  ->
    let topt = FStar_Pervasives_Native.Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____4166 =
      match uu____4166 with
      | (p,i) ->
          let uu____4183 = decorated_pattern_as_term p in
          (match uu____4183 with
           | (vars,te) ->
               let uu____4206 =
                 let uu____4211 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____4211) in
               (vars, uu____4206)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4225 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____4225)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4229 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____4229)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4233 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____4233)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4258 =
          let uu____4273 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____4273 FStar_List.unzip in
        (match uu____4258 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____4385 =
               let uu____4386 =
                 let uu____4387 =
                   let uu____4406 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____4406, args) in
                 FStar_Syntax_Syntax.Tm_app uu____4387 in
               mk1 uu____4386 in
             (vars1, uu____4385))
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
      | (wp,uu____4456)::[] -> wp
      | uu____4481 ->
          let uu____4492 =
            let uu____4493 =
              let uu____4494 =
                FStar_List.map
                  (fun uu____4501  ->
                     match uu____4501 with
                     | (x,uu____4507) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____4494 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4493 in
          failwith uu____4492 in
    let uu____4514 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____4514, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4532 = destruct_comp c in
        match uu____4532 with
        | (u,uu____4540,wp) ->
            let uu____4542 =
              let uu____4553 =
                let uu____4554 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____4554 in
              [uu____4553] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4542;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4564 =
          let uu____4571 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____4572 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____4571 uu____4572 in
        match uu____4564 with | (m,uu____4574,uu____4575) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4585 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____4585
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
        let uu____4622 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4622 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4659 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4659 with
             | (a,kwp) ->
                 let uu____4690 = destruct_comp m1 in
                 let uu____4697 = destruct_comp m2 in
                 ((md, a, kwp), uu____4690, uu____4697))
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
            let uu____4763 =
              let uu____4764 =
                let uu____4775 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4775] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4764;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4763
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
      let uu___128_4816 = lc in
      let uu____4817 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___128_4816.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4817;
        FStar_Syntax_Syntax.cflags =
          (uu___128_4816.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4822  ->
             let uu____4823 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4823)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4827 =
      let uu____4828 = FStar_Syntax_Subst.compress t in
      uu____4828.FStar_Syntax_Syntax.n in
    match uu____4827 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4833 -> true
    | uu____4848 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4862 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4862
        then c
        else
          (let uu____4864 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4864
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4901 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4901] in
                       let us =
                         let uu____4905 =
                           let uu____4908 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4908] in
                         u_res :: uu____4905 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Util.Inr
                                 (FStar_Parser_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____4928 =
                         let uu____4929 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4930 =
                           let uu____4931 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4932 =
                             let uu____4935 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4936 =
                               let uu____4939 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4939] in
                             uu____4935 :: uu____4936 in
                           uu____4931 :: uu____4932 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4929 uu____4930 in
                       uu____4928 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4943 = destruct_comp c1 in
              match uu____4943 with
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
        let close1 uu____4971 =
          let uu____4972 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4972 in
        let uu___129_4973 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_4973.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_4973.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___129_4973.FStar_Syntax_Syntax.cflags);
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
          let uu____4984 =
            let uu____4985 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4985 in
          if uu____4984
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4990 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4990
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4992 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4992 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____5000 =
                        let uu____5001 =
                          let uu____5002 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____5003 =
                            let uu____5004 = FStar_Syntax_Syntax.as_arg t in
                            let uu____5005 =
                              let uu____5008 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____5008] in
                            uu____5004 :: uu____5005 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5002 uu____5003 in
                        uu____5001
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____5000) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____5012 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____5012
         then
           let uu____5013 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____5014 = FStar_Syntax_Print.term_to_string v1 in
           let uu____5015 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____5013
             uu____5014 uu____5015
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
          fun uu____5033  ->
            match uu____5033 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____5046 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____5046
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____5049 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____5051 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____5052 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____5049 uu____5051 bstr uu____5052
                  else ());
                 (let bind_it uu____5057 =
                    let uu____5058 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____5058
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____5072 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____5072
                        then
                          let uu____5073 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____5075 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____5076 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____5077 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____5078 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____5073 uu____5075 uu____5076 uu____5077
                            uu____5078
                        else ());
                       (let try_simplify uu____5095 =
                          let aux uu____5111 =
                            let uu____5112 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____5112
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____5149 ->
                                  let uu____5150 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____5150
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____5185 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____5185
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____5249 =
                                  let uu____5254 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____5254, reason) in
                                FStar_Util.Inl uu____5249
                            | uu____5259 -> aux () in
                          let rec maybe_close t x c =
                            let uu____5278 =
                              let uu____5279 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____5279.FStar_Syntax_Syntax.n in
                            match uu____5278 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____5285) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____5295 -> c in
                          let uu____5296 =
                            let uu____5297 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____5297 in
                          if uu____5296
                          then
                            let uu____5312 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____5312
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____5338 =
                                  let uu____5339 =
                                    let uu____5344 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____5344) in
                                  FStar_Errors.Error uu____5339 in
                                raise uu____5338))
                          else
                            (let uu____5358 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____5358
                             then subst_c2 "both total"
                             else
                               (let uu____5372 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____5372
                                then
                                  let uu____5385 =
                                    let uu____5390 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____5390, "both gtot") in
                                  FStar_Util.Inl uu____5385
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____5418 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____5419 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____5419) in
                                       if uu____5418
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___130_5434 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___130_5434.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___130_5434.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____5435 =
                                           let uu____5440 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____5440, "c1 Tot") in
                                         FStar_Util.Inl uu____5435
                                       else aux ()
                                   | uu____5446 -> aux ()))) in
                        let uu____5455 = try_simplify () in
                        match uu____5455 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____5487 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____5487
                              then
                                let uu____5488 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____5489 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____5490 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____5488 uu____5489 uu____5490
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____5501 = lift_and_destruct env c1 c2 in
                            (match uu____5501 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5558 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____5558]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____5560 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____5560] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr
                                           (FStar_Parser_Const.effect_Tot_lid,
                                             [FStar_Syntax_Syntax.TOTAL]))) in
                                 let r11 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_range r1))
                                     FStar_Pervasives_Native.None r1 in
                                 let wp_args =
                                   let uu____5591 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____5592 =
                                     let uu____5595 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____5596 =
                                       let uu____5599 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____5600 =
                                         let uu____5603 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____5604 =
                                           let uu____5607 =
                                             let uu____5608 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____5608 in
                                           [uu____5607] in
                                         uu____5603 :: uu____5604 in
                                       uu____5599 :: uu____5600 in
                                     uu____5595 :: uu____5596 in
                                   uu____5591 :: uu____5592 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____5615 =
                                     let uu____5616 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____5616
                                       wp_args in
                                   uu____5615 FStar_Pervasives_Native.None
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
              let uu____5656 =
                let uu____5657 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____5657 in
              if uu____5656
              then f
              else (let uu____5659 = reason1 () in label uu____5659 r f)
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
            let uu___131_5670 = g in
            let uu____5671 =
              let uu____5672 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____5672 in
            {
              FStar_TypeChecker_Env.guard_f = uu____5671;
              FStar_TypeChecker_Env.deferred =
                (uu___131_5670.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_5670.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_5670.FStar_TypeChecker_Env.implicits)
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
      | uu____5682 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5703 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5709 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5709
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5720 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5720
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5727 = destruct_comp c1 in
                    match uu____5727 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5747 =
                            let uu____5748 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5749 =
                              let uu____5750 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5751 =
                                let uu____5754 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5755 =
                                  let uu____5758 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5758] in
                                uu____5754 :: uu____5755 in
                              uu____5750 :: uu____5751 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5748
                              uu____5749 in
                          uu____5747 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___132_5761 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_5761.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_5761.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_5761.FStar_Syntax_Syntax.cflags);
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
            let uu____5794 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5794
            then (lc, g0)
            else
              ((let uu____5801 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5801
                then
                  let uu____5802 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5803 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5802 uu____5803
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_5812  ->
                          match uu___98_5812 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5815 -> [])) in
                let strengthen uu____5823 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5835 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5835 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5846 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5847 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5847) in
                           if uu____5846
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5858 =
                                 let uu____5859 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5859 in
                               FStar_Syntax_Util.comp_set_flags uu____5858
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5865 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5865
                           then
                             let uu____5866 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5867 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5866 uu____5867
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5870 = destruct_comp c2 in
                           match uu____5870 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5890 =
                                   let uu____5891 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5892 =
                                     let uu____5893 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5894 =
                                       let uu____5897 =
                                         let uu____5898 =
                                           let uu____5899 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5899 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5898 in
                                       let uu____5900 =
                                         let uu____5903 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5903] in
                                       uu____5897 :: uu____5900 in
                                     uu____5893 :: uu____5894 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5891
                                     uu____5892 in
                                 uu____5890 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5907 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5907
                                 then
                                   let uu____5908 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5908
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5911 =
                  let uu___133_5912 = lc in
                  let uu____5913 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5914 =
                    let uu____5917 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5918 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5918) in
                    if uu____5917 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5913;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___133_5912.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5914;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5911,
                  (let uu___134_5922 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___134_5922.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___134_5922.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___134_5922.FStar_TypeChecker_Env.implicits)
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
        let uu____5939 =
          let uu____5944 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5945 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5944, uu____5945) in
        match uu____5939 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5958 =
                let uu____5959 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5960 =
                  let uu____5961 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5962 =
                    let uu____5965 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5965] in
                  uu____5961 :: uu____5962 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5959 uu____5960 in
              uu____5958 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5973 =
                let uu____5974 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5975 =
                  let uu____5976 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5977 =
                    let uu____5980 =
                      let uu____5981 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5981 in
                    let uu____5982 =
                      let uu____5985 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5985] in
                    uu____5980 :: uu____5982 in
                  uu____5976 :: uu____5977 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5974 uu____5975 in
              uu____5973 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5993 =
                let uu____5994 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5995 =
                  let uu____5996 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5997 =
                    let uu____6000 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____6001 =
                      let uu____6004 =
                        let uu____6005 =
                          let uu____6006 =
                            let uu____6007 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____6007] in
                          FStar_Syntax_Util.abs uu____6006 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Util.Inr
                                  (FStar_Parser_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____6005 in
                      [uu____6004] in
                    uu____6000 :: uu____6001 in
                  uu____5996 :: uu____5997 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5994 uu____5995 in
              uu____5993 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____6030 = FStar_TypeChecker_Env.get_range env in
              bind uu____6030 env FStar_Pervasives_Native.None
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
          let comp uu____6049 =
            let uu____6050 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____6050
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____6053 =
                 let uu____6078 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____6079 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____6078 uu____6079 in
               match uu____6053 with
               | ((md,uu____6081,uu____6082),(u_res_t,res_t,wp_then),
                  (uu____6086,uu____6087,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____6127 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____6128 =
                       let uu____6129 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____6130 =
                         let uu____6131 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____6132 =
                           let uu____6135 = FStar_Syntax_Syntax.as_arg g in
                           let uu____6136 =
                             let uu____6139 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____6140 =
                               let uu____6143 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____6143] in
                             uu____6139 :: uu____6140 in
                           uu____6135 :: uu____6136 in
                         uu____6131 :: uu____6132 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____6129 uu____6130 in
                     uu____6128 FStar_Pervasives_Native.None uu____6127 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____6151 =
                     let uu____6152 = FStar_Options.split_cases () in
                     uu____6152 > (Prims.parse_int "0") in
                   if uu____6151
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____6160 =
                          let uu____6161 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____6162 =
                            let uu____6163 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____6164 =
                              let uu____6167 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____6167] in
                            uu____6163 :: uu____6164 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____6161 uu____6162 in
                        uu____6160 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____6170 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____6170;
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
      let uu____6177 =
        let uu____6178 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____6178 in
      FStar_Syntax_Syntax.fvar uu____6177 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____6206  ->
                 match uu____6206 with
                 | (uu____6211,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____6216 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____6218 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____6218
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____6240 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____6241 =
                 let uu____6242 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____6243 =
                   let uu____6244 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____6245 =
                     let uu____6248 = FStar_Syntax_Syntax.as_arg g in
                     let uu____6249 =
                       let uu____6252 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____6253 =
                         let uu____6256 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____6256] in
                       uu____6252 :: uu____6253 in
                     uu____6248 :: uu____6249 in
                   uu____6244 :: uu____6245 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____6242 uu____6243 in
               uu____6241 FStar_Pervasives_Native.None uu____6240 in
             let default_case =
               let post_k =
                 let uu____6265 =
                   let uu____6272 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____6272] in
                 let uu____6273 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____6265 uu____6273 in
               let kwp =
                 let uu____6283 =
                   let uu____6290 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____6290] in
                 let uu____6291 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____6283 uu____6291 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____6298 =
                   let uu____6299 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____6299] in
                 let uu____6300 =
                   let uu____6301 =
                     let uu____6304 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____6304 in
                   let uu____6305 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____6301 uu____6305 in
                 FStar_Syntax_Util.abs uu____6298 uu____6300
                   (FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                         (FStar_Parser_Const.effect_Tot_lid,
                           [FStar_Syntax_Syntax.TOTAL]))) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Parser_Const.effect_PURE_lid in
               mk_comp md u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____6330  ->
                    fun celse  ->
                      match uu____6330 with
                      | (g,cthen) ->
                          let uu____6338 =
                            let uu____6363 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____6363 celse in
                          (match uu____6338 with
                           | ((md,uu____6365,uu____6366),(uu____6367,uu____6368,wp_then),
                              (uu____6370,uu____6371,wp_else)) ->
                               let uu____6391 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____6391 []))
                 lcases default_case in
             let uu____6392 =
               let uu____6393 = FStar_Options.split_cases () in
               uu____6393 > (Prims.parse_int "0") in
             if uu____6392
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____6397 = destruct_comp comp1 in
                match uu____6397 with
                | (uu____6404,uu____6405,wp) ->
                    let wp1 =
                      let uu____6412 =
                        let uu____6413 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____6414 =
                          let uu____6415 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____6416 =
                            let uu____6419 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____6419] in
                          uu____6415 :: uu____6416 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____6413 uu____6414 in
                      uu____6412 FStar_Pervasives_Native.None
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
          let uu____6434 =
            ((let uu____6435 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____6435) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____6436 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____6436) in
          if uu____6434
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____6447 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____6453 =
            (let uu____6454 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____6454) || env.FStar_TypeChecker_Env.lax in
          if uu____6453
          then c
          else
            (let uu____6460 = FStar_Syntax_Util.is_partial_return c in
             if uu____6460
             then c
             else
               (let uu____6466 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____6466
                then
                  let uu____6471 =
                    let uu____6472 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____6472 in
                  (if uu____6471
                   then
                     let uu____6477 =
                       let uu____6478 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____6479 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____6478 uu____6479 in
                     failwith uu____6477
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____6486 =
                        let uu____6487 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____6487 in
                      if uu____6486
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___135_6494 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___135_6494.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___135_6494.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___135_6494.FStar_Syntax_Syntax.effect_args);
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
                     let uu____6507 =
                       let uu____6512 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____6512
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____6507 in
                   let eq1 =
                     let uu____6518 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____6518 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____6520 =
                     let uu____6521 =
                       let uu____6528 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____6528.FStar_Syntax_Syntax.comp in
                     uu____6521 () in
                   FStar_Syntax_Util.comp_set_flags uu____6520 flags))) in
        let uu___136_6531 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_6531.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_6531.FStar_Syntax_Syntax.res_typ);
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
          let uu____6556 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6556 with
          | FStar_Pervasives_Native.None  ->
              let uu____6565 =
                let uu____6566 =
                  let uu____6571 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____6572 = FStar_TypeChecker_Env.get_range env in
                  (uu____6571, uu____6572) in
                FStar_Errors.Error uu____6566 in
              raise uu____6565
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
            let uu____6605 =
              let uu____6606 = FStar_Syntax_Subst.compress t2 in
              uu____6606.FStar_Syntax_Syntax.n in
            match uu____6605 with
            | FStar_Syntax_Syntax.Tm_type uu____6611 -> true
            | uu____6612 -> false in
          let uu____6613 =
            let uu____6614 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____6614.FStar_Syntax_Syntax.n in
          match uu____6613 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6624 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6635 =
                  let uu____6636 =
                    let uu____6637 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6637 in
                  (FStar_Pervasives_Native.None, uu____6636) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6635 in
              let e1 =
                let uu____6653 =
                  let uu____6654 =
                    let uu____6655 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6655] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6654 in
                uu____6653
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6662 -> (e, lc)
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
              (let uu____6688 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6688 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6711 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6733 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6733, false)
            else
              (let uu____6739 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6739, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6750) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___137_6754 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___137_6754.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___137_6754.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___137_6754.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6759 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6759 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___138_6767 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___138_6767.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___138_6767.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___138_6767.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_6770 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_6770.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_6770.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_6770.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6778 =
                     let uu____6779 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6779
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____6786 =
                          let uu____6787 = FStar_Syntax_Subst.compress f1 in
                          uu____6787.FStar_Syntax_Syntax.n in
                        match uu____6786 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6796,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____6798;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6799;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6800;_},uu____6801)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_6847 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___140_6847.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___140_6847.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___140_6847.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6848 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6855 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6855
                              then
                                let uu____6856 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6857 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6858 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6859 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6856 uu____6857 uu____6858 uu____6859
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6862 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6862 with
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
                                  let uu____6877 = destruct_comp ct in
                                  (match uu____6877 with
                                   | (u_t,uu____6889,uu____6890) ->
                                       let wp =
                                         let uu____6896 =
                                           let uu____6897 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6898 =
                                             let uu____6899 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6900 =
                                               let uu____6903 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6903] in
                                             uu____6899 :: uu____6900 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6897 uu____6898 in
                                         uu____6896
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6907 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6907 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6925 =
                                             let uu____6926 =
                                               let uu____6927 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6927] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6926 in
                                           uu____6925
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6931 =
                                         let uu____6936 =
                                           FStar_All.pipe_left
                                             (fun _0_29  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6949 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6950 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6936
                                           uu____6949 e cret uu____6950 in
                                       (match uu____6931 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___141_6958 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___141_6958.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___141_6958.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6960 =
                                                let uu____6961 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6961 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6960
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6978 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6978
                                              then
                                                let uu____6979 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6979
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_6988  ->
                             match uu___99_6988 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6991 -> [])) in
                   let lc1 =
                     let uu___142_6993 = lc in
                     let uu____6994 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6994;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___143_6996 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_6996.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_6996.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_6996.FStar_TypeChecker_Env.implicits)
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
        let uu____7021 =
          let uu____7022 =
            let uu____7023 =
              let uu____7024 =
                let uu____7025 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____7025 in
              [uu____7024] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7023 in
          uu____7022 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____7021 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____7032 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____7032
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7052 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7069 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7100)::(ens,uu____7102)::uu____7103 ->
                    let uu____7146 =
                      let uu____7149 = norm req in
                      FStar_Pervasives_Native.Some uu____7149 in
                    let uu____7150 =
                      let uu____7151 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____7151 in
                    (uu____7146, uu____7150)
                | uu____7154 ->
                    let uu____7165 =
                      let uu____7166 =
                        let uu____7171 =
                          let uu____7172 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____7172 in
                        (uu____7171, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____7166 in
                    raise uu____7165)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7188)::uu____7189 ->
                    let uu____7216 =
                      let uu____7221 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7221 in
                    (match uu____7216 with
                     | (us_r,uu____7253) ->
                         let uu____7254 =
                           let uu____7259 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7259 in
                         (match uu____7254 with
                          | (us_e,uu____7291) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____7294 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7294
                                  us_r in
                              let as_ens =
                                let uu____7296 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7296
                                  us_e in
                              let req =
                                let uu____7302 =
                                  let uu____7303 =
                                    let uu____7304 =
                                      let uu____7317 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____7317] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7304 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7303 in
                                uu____7302
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____7341 =
                                  let uu____7342 =
                                    let uu____7343 =
                                      let uu____7356 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____7356] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7343 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7342 in
                                uu____7341 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____7375 =
                                let uu____7378 = norm req in
                                FStar_Pervasives_Native.Some uu____7378 in
                              let uu____7379 =
                                let uu____7380 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____7380 in
                              (uu____7375, uu____7379)))
                | uu____7383 -> failwith "Impossible"))
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
      (let uu____7413 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____7413
       then
         let uu____7414 = FStar_Syntax_Print.term_to_string tm in
         let uu____7415 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7414 uu____7415
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
        (let uu____7435 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____7435
         then
           let uu____7436 = FStar_Syntax_Print.term_to_string tm in
           let uu____7437 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7436
             uu____7437
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____7442 =
      let uu____7443 =
        let uu____7444 = FStar_Syntax_Subst.compress t in
        uu____7444.FStar_Syntax_Syntax.n in
      match uu____7443 with
      | FStar_Syntax_Syntax.Tm_app uu____7449 -> false
      | uu____7468 -> true in
    if uu____7442
    then t
    else
      (let uu____7470 = FStar_Syntax_Util.head_and_args t in
       match uu____7470 with
       | (head1,args) ->
           let uu____7519 =
             let uu____7520 =
               let uu____7521 = FStar_Syntax_Subst.compress head1 in
               uu____7521.FStar_Syntax_Syntax.n in
             match uu____7520 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7526 -> false in
           if uu____7519
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7556 ->
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
             let uu____7595 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____7595 with
             | (formals,uu____7611) ->
                 let n_implicits =
                   let uu____7633 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7706  ->
                             match uu____7706 with
                             | (uu____7713,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7633 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7843 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7843 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7860 =
                     let uu____7861 =
                       let uu____7866 =
                         let uu____7867 = FStar_Util.string_of_int n_expected in
                         let uu____7871 = FStar_Syntax_Print.term_to_string e in
                         let uu____7872 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7867 uu____7871 uu____7872 in
                       let uu____7876 = FStar_TypeChecker_Env.get_range env in
                       (uu____7866, uu____7876) in
                     FStar_Errors.Error uu____7861 in
                   raise uu____7860
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___100_7892 =
             match uu___100_7892 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7926 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7926 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_30,uu____8035) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8078,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____8111 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____8111 with
                           | (v1,uu____8151,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____8168 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____8168 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8261 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8261)))
                      | (uu____8288,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____8334 =
                      let uu____8361 = inst_n_binders t in
                      aux [] uu____8361 bs1 in
                    (match uu____8334 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8432) -> (e, torig, guard)
                          | (uu____8463,[]) when
                              let uu____8494 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____8494 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8495 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8531 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____8550 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____8566 =
    let uu____8569 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____8569
      (FStar_List.map
         (fun u  ->
            let uu____8587 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____8587 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____8566 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____8604 = FStar_Util.set_is_empty x in
      if uu____8604
      then []
      else
        (let s =
           let uu____8611 =
             let uu____8614 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____8614 in
           FStar_All.pipe_right uu____8611 FStar_Util.set_elements in
         (let uu____8622 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____8622
          then
            let uu____8623 =
              let uu____8624 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8624 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8623
          else ());
         (let r =
            let uu____8637 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8637 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8656 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8656
                     then
                       let uu____8657 =
                         let uu____8658 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8658 in
                       let uu____8661 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8662 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8657 uu____8661 uu____8662
                     else ());
                    FStar_Unionfind.change u
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.U_name u_name));
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
        let uu____8686 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8686 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_8724 =
  match uu___101_8724 with
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
        | ([],uu____8780) -> generalized_univ_names
        | (uu____8787,[]) -> explicit_univ_names
        | uu____8794 ->
            let uu____8803 =
              let uu____8804 =
                let uu____8809 =
                  let uu____8810 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____8810 in
                (uu____8809, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____8804 in
            raise uu____8803
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
      (let uu____8827 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8827
       then
         let uu____8828 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8828
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8836 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8836
        then
          let uu____8837 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8837
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____8843 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____8843))
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
      let uu____8892 =
        let uu____8893 =
          FStar_Util.for_all
            (fun uu____8902  ->
               match uu____8902 with
               | (uu____8911,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____8893 in
      if uu____8892
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____8949 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____8949
            then
              let uu____8950 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____8950
            else ());
           (let c1 =
              let uu____8953 = FStar_TypeChecker_Env.should_verify env in
              if uu____8953
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
            (let uu____8956 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____8956
             then
               let uu____8957 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8957
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____9018 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____9018 FStar_Util.set_elements in
         let uu____9105 =
           let uu____9140 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____9249  ->
                     match uu____9249 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         let uvs = gen_uvars uvt in (univs1, (uvs, e, c1)))) in
           FStar_All.pipe_right uu____9140 FStar_List.unzip in
         match uu____9105 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____9559 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____9559
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
                      (fun uu____9639  ->
                         match uu____9639 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____9748  ->
                                       match uu____9748 with
                                       | (u,k) ->
                                           let uu____9785 =
                                             FStar_Unionfind.find u in
                                           (match uu____9785 with
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____9805;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9806;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9807;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____9818,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____9820;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____9821;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____9822;_},uu____9823);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____9824;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____9825;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____9826;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____9881 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____9896 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____9904 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____9904 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____9948 =
                                                         let uu____9951 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_31)
                                                           uu____9951 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____9948 kres in
                                                     let t =
                                                       let uu____9955 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____9956 =
                                                         let uu____9969 =
                                                           let uu____9980 =
                                                             let uu____9981 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____9981 in
                                                           FStar_Util.Inl
                                                             uu____9980 in
                                                         FStar_Pervasives_Native.Some
                                                           uu____9969 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____9955
                                                         uu____9956 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____10009 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____10044 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____10044, c)
                               | ([],uu____10045) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm;
                                       FStar_TypeChecker_Normalize.Exclude
                                         FStar_TypeChecker_Normalize.Zeta]
                                       env c in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (e1, c1)
                               | uu____10066 ->
                                   let uu____10081 = (e, c) in
                                   (match uu____10081 with
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
                                          let uu____10099 =
                                            let uu____10100 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____10100.FStar_Syntax_Syntax.n in
                                          match uu____10099 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10131 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____10131 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____10148 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____10166 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____10166)) in
                             (match uu____10009 with
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
      (let uu____10232 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____10232
       then
         let uu____10233 =
           let uu____10234 =
             FStar_List.map
               (fun uu____10243  ->
                  match uu____10243 with
                  | (lb,uu____10251,uu____10252) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____10234 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____10233
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____10269  ->
              match uu____10269 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____10294 =
           let uu____10307 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____10338  ->
                     match uu____10338 with | (uu____10349,e,c) -> (e, c))) in
           gen env uu____10307 in
         match uu____10294 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____10410  ->
                     match uu____10410 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____10493  ->
                  fun uu____10494  ->
                    match (uu____10493, uu____10494) with
                    | ((l,uu____10558,uu____10559),(us,e,c)) ->
                        ((let uu____10606 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____10606
                          then
                            let uu____10607 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____10608 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____10609 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____10610 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____10607 uu____10608 uu____10609 uu____10610
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____10645  ->
              match uu____10645 with
              | (l,generalized_univs,t,c) ->
                  let uu____10676 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____10676, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____10717 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____10717 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10723 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                     uu____10723) in
          let is_var e1 =
            let uu____10730 =
              let uu____10731 = FStar_Syntax_Subst.compress e1 in
              uu____10731.FStar_Syntax_Syntax.n in
            match uu____10730 with
            | FStar_Syntax_Syntax.Tm_name uu____10736 -> true
            | uu____10737 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___144_10755 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_10755.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_10755.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____10756 ->
                let uu___145_10757 = e2 in
                let uu____10758 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_10757.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____10758;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_10757.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_10757.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___146_10766 = env1 in
            let uu____10767 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_10766.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_10766.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_10766.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_10766.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_10766.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_10766.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_10766.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_10766.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_10766.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_10766.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_10766.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_10766.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_10766.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_10766.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_10766.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10767;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_10766.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_10766.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_10766.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_10766.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_10766.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_10766.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_10766.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_10766.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____10768 = check env2 t1 t2 in
          match uu____10768 with
          | FStar_Pervasives_Native.None  ->
              let uu____10775 =
                let uu____10776 =
                  let uu____10781 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10782 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10781, uu____10782) in
                FStar_Errors.Error uu____10776 in
              raise uu____10775
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10789 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10789
                then
                  let uu____10790 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10790
                else ());
               (let uu____10792 = decorate e t2 in (uu____10792, g)))
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
        let uu____10824 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10824
        then
          let uu____10829 = discharge g1 in
          let uu____10830 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10829, uu____10830)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10849 =
               let uu____10850 =
                 let uu____10851 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10851 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10850
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10849
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10853 = destruct_comp c1 in
           match uu____10853 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10872 = FStar_TypeChecker_Env.get_range env in
                 let uu____10873 =
                   let uu____10874 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10875 =
                     let uu____10876 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10877 =
                       let uu____10880 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10880] in
                     uu____10876 :: uu____10877 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10874 uu____10875 in
                 uu____10873
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____10872 in
               ((let uu____10884 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10884
                 then
                   let uu____10885 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10885
                 else ());
                (let g2 =
                   let uu____10888 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10888 in
                 let uu____10889 = discharge g2 in
                 let uu____10890 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10889, uu____10890))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_10918 =
        match uu___102_10918 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10928)::[] -> f fst1
        | uu____10953 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10958 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10958
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____10971 =
          let uu____10976 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10976 in
        FStar_All.pipe_right uu____10971
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____10989 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10989
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_11009 =
        match uu___103_11009 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11019)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11046)::[] ->
            let uu____11087 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____11087
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____11096 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____11106 =
          let uu____11113 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____11113) in
        let uu____11118 =
          let uu____11127 =
            let uu____11134 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____11134) in
          let uu____11139 =
            let uu____11148 =
              let uu____11155 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____11155) in
            let uu____11160 =
              let uu____11169 =
                let uu____11176 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____11176) in
              let uu____11181 =
                let uu____11190 =
                  let uu____11197 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____11197) in
                [uu____11190; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____11169 :: uu____11181 in
            uu____11148 :: uu____11160 in
          uu____11127 :: uu____11139 in
        uu____11106 :: uu____11118 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____11252 =
            FStar_Util.find_map table
              (fun uu____11261  ->
                 match uu____11261 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11278 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____11278
                     else FStar_Pervasives_Native.None) in
          (match uu____11252 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11281 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____11285 =
      let uu____11286 = FStar_Syntax_Util.un_uinst l in
      uu____11286.FStar_Syntax_Syntax.n in
    match uu____11285 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11292 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11316)::uu____11317 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11328 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____11335,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11336))::uu____11337 -> bs
      | uu____11354 ->
          let uu____11355 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11355 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11359 =
                 let uu____11360 = FStar_Syntax_Subst.compress t in
                 uu____11360.FStar_Syntax_Syntax.n in
               (match uu____11359 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11366) ->
                    let uu____11387 =
                      FStar_Util.prefix_until
                        (fun uu___104_11424  ->
                           match uu___104_11424 with
                           | (uu____11431,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11432)) ->
                               false
                           | uu____11435 -> true) bs' in
                    (match uu____11387 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11470,uu____11471) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11543,uu____11544) ->
                         let uu____11617 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11632  ->
                                   match uu____11632 with
                                   | (x,uu____11640) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11617
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11683  ->
                                     match uu____11683 with
                                     | (x,i) ->
                                         let uu____11702 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11702, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11712 -> bs))
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
              (let uu____11731 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____11731 e.FStar_Syntax_Syntax.pos)
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
          let uu____11749 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11749
          then e
          else
            (let uu____11751 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____11751
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
        (let uu____11777 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11777
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11779 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11779))
         else ());
        (let fv =
           let uu____11782 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11782
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
             (FStar_Syntax_Syntax.Sig_let (lb, [lident], [])) in
         let uu____11792 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___147_11801 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_11801.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_11801.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_11801.FStar_Syntax_Syntax.sigmeta)
           }), uu____11792))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_11811 =
        match uu___105_11811 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11812 -> false in
      let reducibility uu___106_11816 =
        match uu___106_11816 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11817 -> false in
      let assumption uu___107_11821 =
        match uu___107_11821 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11822 -> false in
      let reification uu___108_11826 =
        match uu___108_11826 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11827 -> true
        | uu____11828 -> false in
      let inferred uu___109_11832 =
        match uu___109_11832 with
        | FStar_Syntax_Syntax.Discriminator uu____11833 -> true
        | FStar_Syntax_Syntax.Projector uu____11834 -> true
        | FStar_Syntax_Syntax.RecordType uu____11839 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11848 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11857 -> false in
      let has_eq uu___110_11861 =
        match uu___110_11861 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11862 -> false in
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
        | uu____11914 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11918 =
        let uu____11919 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_11922  ->
                  match uu___111_11922 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11923 -> false)) in
        FStar_All.pipe_right uu____11919 Prims.op_Negation in
      if uu____11918
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11934 =
            let uu____11935 =
              let uu____11940 =
                let uu____11941 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11941 msg in
              (uu____11940, r) in
            FStar_Errors.Error uu____11935 in
          raise uu____11934 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11949 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11953 =
            let uu____11954 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11954 in
          if uu____11953 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____11959),uu____11960,uu____11961) ->
              ((let uu____11981 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11981
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11985 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11985
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
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12005 ->
              let uu____12012 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____12012 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12016 ->
              let uu____12021 =
                let uu____12022 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____12022 in
              if uu____12021 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12027 ->
              let uu____12028 =
                let uu____12029 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____12029 in
              if uu____12028 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12034 ->
              let uu____12035 =
                let uu____12036 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____12036 in
              if uu____12035 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12041 ->
              let uu____12054 =
                let uu____12055 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____12055 in
              if uu____12054 then err'1 () else ()
          | uu____12060 -> ()))
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
                      let pos q =
                        FStar_Syntax_Syntax.withinfo q
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          let uu____12128 =
                            let uu____12133 =
                              let uu____12134 =
                                let uu____12143 =
                                  let uu____12144 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____12144 in
                                (uu____12143, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____12134 in
                            FStar_Syntax_Syntax.mk uu____12133 in
                          uu____12128 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____12182  ->
                                  match uu____12182 with
                                  | (x,imp) ->
                                      let uu____12193 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____12193, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____12195 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____12195 in
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
                             let uu____12206 =
                               let uu____12207 =
                                 let uu____12208 =
                                   let uu____12209 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____12210 =
                                     let uu____12211 =
                                       let uu____12212 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____12212 in
                                     [uu____12211] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____12209
                                     uu____12210 in
                                 uu____12208 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____12207 in
                             FStar_Syntax_Util.refine x uu____12206 in
                           let uu____12215 =
                             let uu___148_12216 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_12216.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_12216.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____12215) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____12231 =
                          FStar_List.map
                            (fun uu____12250  ->
                               match uu____12250 with
                               | (x,uu____12262) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____12231 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12308  ->
                                match uu____12308 with
                                | (x,uu____12320) ->
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
                             (let uu____12332 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12332)
                               ||
                               (let uu____12333 =
                                  let uu____12334 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12334.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12333) in
                           let quals =
                             let uu____12338 =
                               let uu____12341 =
                                 let uu____12344 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12344
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12348 =
                                 FStar_List.filter
                                   (fun uu___112_12351  ->
                                      match uu___112_12351 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12352 -> false) iquals in
                               FStar_List.append uu____12341 uu____12348 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12338 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12373 =
                                 let uu____12374 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12374 in
                               FStar_Syntax_Syntax.mk_Total uu____12373 in
                             let uu____12375 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12375 in
                           let decl =
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng =
                                 (FStar_Ident.range_of_lid discriminator_name);
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta
                             } in
                           (let uu____12378 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12378
                            then
                              let uu____12379 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12379
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
                                             fun uu____12436  ->
                                               match uu____12436 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12462 =
                                                       let uu____12467 =
                                                         let uu____12468 =
                                                           let uu____12477 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12477,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12468 in
                                                       pos uu____12467 in
                                                     (uu____12462, b)
                                                   else
                                                     (let uu____12483 =
                                                        let uu____12488 =
                                                          let uu____12489 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12489 in
                                                        pos uu____12488 in
                                                      (uu____12483, b)))) in
                                   let pat_true =
                                     let uu____12515 =
                                       let uu____12520 =
                                         let uu____12521 =
                                           let uu____12536 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12536, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12521 in
                                       pos uu____12520 in
                                     (uu____12515,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12586 =
                                       let uu____12591 =
                                         let uu____12592 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12592 in
                                       pos uu____12591 in
                                     (uu____12586,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12612 =
                                     let uu____12617 =
                                       let uu____12618 =
                                         let uu____12649 =
                                           let uu____12652 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12653 =
                                             let uu____12656 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12656] in
                                           uu____12652 :: uu____12653 in
                                         (arg_exp, uu____12649) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12618 in
                                     FStar_Syntax_Syntax.mk uu____12617 in
                                   uu____12612 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12664 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12664
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
                                let uu____12682 =
                                  let uu____12687 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12687 in
                                let uu____12688 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12682;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12688
                                } in
                              let impl =
                                let uu____12694 =
                                  let uu____12695 =
                                    let uu____12706 =
                                      let uu____12709 =
                                        let uu____12710 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12710
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12709] in
                                    ((false, [lb]), uu____12706, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____12695 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12694;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____12733 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12733
                               then
                                 let uu____12734 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12734
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
                                fun uu____12767  ->
                                  match uu____12767 with
                                  | (a,uu____12773) ->
                                      let uu____12774 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12774 with
                                       | (field_name,uu____12780) ->
                                           let field_proj_tm =
                                             let uu____12782 =
                                               let uu____12783 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12783 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12782 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12804 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12820  ->
                                    match uu____12820 with
                                    | (x,uu____12828) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12830 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12830 with
                                         | (field_name,uu____12838) ->
                                             let t =
                                               let uu____12840 =
                                                 let uu____12841 =
                                                   let uu____12846 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12846 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12841 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12840 in
                                             let only_decl =
                                               ((let uu____12848 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Parser_Const.prims_lid
                                                   uu____12848)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____12849 =
                                                    let uu____12850 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12850.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12849) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12864 =
                                                   FStar_List.filter
                                                     (fun uu___113_12867  ->
                                                        match uu___113_12867
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12868 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12864
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_12880  ->
                                                         match uu___114_12880
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12881 ->
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
                                                   FStar_Syntax_Syntax.default_sigmeta
                                               } in
                                             ((let uu____12884 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12884
                                               then
                                                 let uu____12885 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12885
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
                                                           fun uu____12933 
                                                             ->
                                                             match uu____12933
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12959
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12959,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12979
                                                                    =
                                                                    let uu____12984
                                                                    =
                                                                    let uu____12985
                                                                    =
                                                                    let uu____12994
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12994,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12985 in
                                                                    pos
                                                                    uu____12984 in
                                                                    (uu____12979,
                                                                    b))
                                                                   else
                                                                    (let uu____13000
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
                                                                    (uu____13000,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____13028 =
                                                     let uu____13033 =
                                                       let uu____13034 =
                                                         let uu____13049 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____13049,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____13034 in
                                                     pos uu____13033 in
                                                   let uu____13060 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____13028,
                                                     FStar_Pervasives_Native.None,
                                                     uu____13060) in
                                                 let body =
                                                   let uu____13080 =
                                                     let uu____13085 =
                                                       let uu____13086 =
                                                         let uu____13117 =
                                                           let uu____13120 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____13120] in
                                                         (arg_exp,
                                                           uu____13117) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____13086 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____13085 in
                                                   uu____13080
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____13139 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____13139
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
                                                   let uu____13146 =
                                                     let uu____13151 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____13151 in
                                                   let uu____13152 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____13146;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____13152
                                                   } in
                                                 let impl =
                                                   let uu____13158 =
                                                     let uu____13159 =
                                                       let uu____13170 =
                                                         let uu____13173 =
                                                           let uu____13174 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____13174
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____13173] in
                                                       ((false, [lb]),
                                                         uu____13170, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____13159 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____13158;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____13197 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____13197
                                                  then
                                                    let uu____13198 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____13198
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12804 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____13238) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____13243 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____13243 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____13265 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____13265 with
                    | (formals,uu____13283) ->
                        let uu____13304 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____13327 =
                                   let uu____13328 =
                                     let uu____13329 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____13329 in
                                   FStar_Ident.lid_equals typ_lid uu____13328 in
                                 if uu____13327
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____13348,uvs',tps,typ0,uu____13352,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____13371 -> failwith "Impossible"
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
                        (match uu____13304 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13446 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13446 with
                              | (indices,uu____13464) ->
                                  let refine_domain =
                                    let uu____13486 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_13489  ->
                                              match uu___115_13489 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13490 -> true
                                              | uu____13499 -> false)) in
                                    if uu____13486
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_13507 =
                                      match uu___116_13507 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13510,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13522 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13523 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13523 with
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
                                    let uu____13534 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13534 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13592  ->
                                               fun uu____13593  ->
                                                 match (uu____13592,
                                                         uu____13593)
                                                 with
                                                 | ((x,uu____13611),(x',uu____13613))
                                                     ->
                                                     let uu____13622 =
                                                       let uu____13631 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13631) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13622) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13632 -> []