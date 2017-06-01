open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____12 = FStar_TypeChecker_Env.get_range env in
      let uu____13 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____12 uu____13
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____17 =
      let uu____18 = FStar_Syntax_Subst.compress t in
      uu____18.FStar_Syntax_Syntax.n in
    match uu____17 with
    | FStar_Syntax_Syntax.Tm_type uu____21 -> true
    | uu____22 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____29 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____29
      (FStar_List.filter
         (fun uu____35  ->
            match uu____35 with
            | (x,uu____39) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____49 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____50 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____50) in
        if uu____49
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____52 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____52 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____59 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____59
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___97_64  ->
    match uu___97_64 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____66);
        FStar_Syntax_Syntax.tk = uu____67;
        FStar_Syntax_Syntax.pos = uu____68;
        FStar_Syntax_Syntax.vars = uu____69;_} -> uv
    | uu____84 -> failwith "Impossible"
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
          let uu____103 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____103 with
          | FStar_Pervasives_Native.Some (uu____116::(tm,uu____118)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____158 ->
              let uu____165 = new_uvar_aux env k in
              (match uu____165 with
               | (t,u) ->
                   let g =
                     let uu___117_177 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____178 =
                       let uu____186 =
                         let uu____193 = as_uvar u in
                         (reason, env, uu____193, t, k, r) in
                       [uu____186] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___117_177.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___117_177.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___117_177.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____178
                     } in
                   let uu____206 =
                     let uu____210 =
                       let uu____213 = as_uvar u in (uu____213, r) in
                     [uu____210] in
                   (t, uu____206, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____231 =
        let uu____232 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____232 in
      if uu____231
      then
        let us =
          let uu____236 =
            let uu____238 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____254  ->
                 match uu____254 with
                 | (x,uu____262) -> FStar_Syntax_Print.uvar_to_string x)
              uu____238 in
          FStar_All.pipe_right uu____236 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____279 =
            let uu____280 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____280 in
          FStar_Errors.err r uu____279);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____289 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____289 with
    | FStar_Pervasives_Native.None  ->
        let uu____294 =
          let uu____295 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____296 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____295 uu____296 in
        failwith uu____294
    | FStar_Pervasives_Native.Some tk -> tk
let force_sort s =
  let uu____311 =
    let uu____314 = force_sort' s in FStar_Syntax_Syntax.mk uu____314 in
  uu____311 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____331  ->
      match uu____331 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____338;
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
                   let uu____370 =
                     let uu____371 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____371.FStar_Syntax_Syntax.n in
                   match uu____370 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____376 = FStar_Syntax_Util.type_u () in
                       (match uu____376 with
                        | (k,uu____382) ->
                            let t2 =
                              let uu____384 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____384
                                FStar_Pervasives_Native.fst in
                            ((let uu___118_389 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_389.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_389.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____390 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____415) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____422) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____468) ->
                       let uu____491 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____515  ->
                                 fun uu____516  ->
                                   match (uu____515, uu____516) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____558 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____558 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____491 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____619 = aux must_check_ty1 scope body in
                            (match uu____619 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____636 =
                                         FStar_Options.ml_ish () in
                                       if uu____636
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____643 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____643
                                   then
                                     let uu____644 =
                                       FStar_Range.string_of_range r in
                                     let uu____645 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____646 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____644 uu____645 uu____646
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____654 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____662 =
                            let uu____665 =
                              let uu____666 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____666
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____665 in
                          (uu____662, false)) in
                 let uu____673 =
                   let uu____678 = t_binders env in aux false uu____678 e in
                 match uu____673 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____695 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____695
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____699 =
                                let uu____700 =
                                  let uu____703 =
                                    let uu____704 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____704 in
                                  (uu____703, rng) in
                                FStar_Errors.Error uu____700 in
                              raise uu____699)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____711 ->
               let uu____712 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____712 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____793) ->
              let uu____798 = FStar_Syntax_Util.type_u () in
              (match uu____798 with
               | (k,uu____811) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_814 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_814.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_814.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____815 =
                     let uu____818 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____818 t in
                   (match uu____815 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_833 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___120_833.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___120_833.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____840 = FStar_Syntax_Util.type_u () in
              (match uu____840 with
               | (t,uu____853) ->
                   let x1 =
                     let uu___121_855 = x in
                     let uu____856 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_855.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_855.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____856
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
              let uu____878 = FStar_Syntax_Util.type_u () in
              (match uu____878 with
               | (t,uu____891) ->
                   let x1 =
                     let uu___122_893 = x in
                     let uu____894 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_893.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_893.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____894
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____926 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____982  ->
                        fun uu____983  ->
                          match (uu____982, uu____983) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1082 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1082 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____926 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1190 =
                       let uu____1193 =
                         let uu____1194 =
                           let uu____1199 =
                             let uu____1202 =
                               let uu____1203 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1204 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1203
                                 uu____1204 in
                             uu____1202 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1199,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1194 in
                       FStar_Syntax_Syntax.mk uu____1193 in
                     uu____1190 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1221 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1227 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1233 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1221, uu____1227, uu____1233, env2, e,
                     (let uu___123_1246 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___123_1246.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___123_1246.FStar_Syntax_Syntax.p)
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
                  (fun uu____1308  ->
                     match uu____1308 with
                     | (p2,imp) ->
                         let uu____1323 = elaborate_pat env1 p2 in
                         (uu____1323, imp)) pats in
              let uu____1328 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1328 with
               | (uu____1337,t) ->
                   let uu____1339 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1339 with
                    | (f,uu____1350) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1425::uu____1426) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1461::uu____1462,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1502  ->
                                      match uu____1502 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1520 =
                                                   let uu____1522 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____1522 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1520
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1528 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1528, true)
                                           | uu____1533 ->
                                               let uu____1535 =
                                                 let uu____1536 =
                                                   let uu____1539 =
                                                     let uu____1540 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1540 in
                                                   (uu____1539,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1536 in
                                               raise uu____1535)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1591,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____1592))
                                   when p_imp ->
                                   let uu____1594 = aux formals' pats' in
                                   (p2, true) :: uu____1594
                               | (uu____1606,FStar_Pervasives_Native.Some
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
                                   let uu____1617 = aux formals' pats2 in
                                   (p3, true) :: uu____1617
                               | (uu____1629,imp) ->
                                   let uu____1633 =
                                     let uu____1638 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1638) in
                                   let uu____1641 = aux formals' pats' in
                                   uu____1633 :: uu____1641) in
                        let uu___124_1651 = p1 in
                        let uu____1654 =
                          let uu____1655 =
                            let uu____1663 = aux f pats1 in (fv, uu____1663) in
                          FStar_Syntax_Syntax.Pat_cons uu____1655 in
                        {
                          FStar_Syntax_Syntax.v = uu____1654;
                          FStar_Syntax_Syntax.ty =
                            (uu___124_1651.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___124_1651.FStar_Syntax_Syntax.p)
                        }))
          | uu____1674 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1700 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1700 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1730 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1730 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____1743 =
                     let uu____1744 =
                       let uu____1747 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1747, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1744 in
                   raise uu____1743
               | uu____1756 -> (b, a, w, arg, p3)) in
        let uu____1761 = one_pat true env p in
        match uu____1761 with
        | (b,uu____1775,uu____1776,tm,p1) -> (b, tm, p1)
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
          | (uu____1817,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1819)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1824,FStar_Syntax_Syntax.Tm_constant uu____1825) ->
              let uu____1826 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1826
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1830 =
                    let uu____1831 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1832 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1831 uu____1832 in
                  failwith uu____1830)
               else ();
               (let uu____1835 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1835
                then
                  let uu____1836 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1837 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1836
                    uu____1837
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_1841 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_1841.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_1841.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1845 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1845
                then
                  let uu____1846 =
                    let uu____1847 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1848 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1847 uu____1848 in
                  failwith uu____1846
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1852 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1852.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1852.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1854),uu____1855) ->
              let s = force_sort e1 in
              let x1 =
                let uu___127_1864 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___127_1864.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___127_1864.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1877 =
                  let uu____1878 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1878 in
                if uu____1877
                then
                  let uu____1879 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1879
                else ());
               (let uu____1889 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1889))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1902;
                FStar_Syntax_Syntax.pos = uu____1903;
                FStar_Syntax_Syntax.vars = uu____1904;_},args))
              ->
              ((let uu____1931 =
                  let uu____1932 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1932 Prims.op_Negation in
                if uu____1931
                then
                  let uu____1933 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1933
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2021 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2021
                  | (arg::args2,(argpat,uu____2034)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2084) ->
                           let x =
                             let uu____2100 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____2100 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2114) ->
                           let pat =
                             let uu____2129 = aux argpat e2 in
                             let uu____2130 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2129, uu____2130) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2133 ->
                      let uu____2147 =
                        let uu____2148 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2149 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2148 uu____2149 in
                      failwith uu____2147 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2159;
                     FStar_Syntax_Syntax.pos = uu____2160;
                     FStar_Syntax_Syntax.vars = uu____2161;_},uu____2162);
                FStar_Syntax_Syntax.tk = uu____2163;
                FStar_Syntax_Syntax.pos = uu____2164;
                FStar_Syntax_Syntax.vars = uu____2165;_},args))
              ->
              ((let uu____2196 =
                  let uu____2197 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2197 Prims.op_Negation in
                if uu____2196
                then
                  let uu____2198 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2198
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2286 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2286
                  | (arg::args2,(argpat,uu____2299)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2349) ->
                           let x =
                             let uu____2365 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____2365 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2379) ->
                           let pat =
                             let uu____2394 = aux argpat e2 in
                             let uu____2395 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2394, uu____2395) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2398 ->
                      let uu____2412 =
                        let uu____2413 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2414 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2413 uu____2414 in
                      failwith uu____2412 in
                match_args [] args argpats))
          | uu____2421 ->
              let uu____2424 =
                let uu____2425 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2426 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2427 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2425 uu____2426 uu____2427 in
              failwith uu____2424 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun pat  ->
    let topt = FStar_Pervasives_Native.Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2461 =
      match uu____2461 with
      | (p,i) ->
          let uu____2471 = decorated_pattern_as_term p in
          (match uu____2471 with
           | (vars,te) ->
               let uu____2484 =
                 let uu____2487 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2487) in
               (vars, uu____2484)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2495 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2495)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2498 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2498)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2501 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2501)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2515 =
          let uu____2523 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2523 FStar_List.unzip in
        (match uu____2515 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2581 =
               let uu____2582 =
                 let uu____2583 =
                   let uu____2593 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2593, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2583 in
               mk1 uu____2582 in
             (vars1, uu____2581))
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
      | (wp,uu____2622)::[] -> wp
      | uu____2635 ->
          let uu____2641 =
            let uu____2642 =
              let uu____2643 =
                FStar_List.map
                  (fun uu____2647  ->
                     match uu____2647 with
                     | (x,uu____2651) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2643 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2642 in
          failwith uu____2641 in
    let uu____2655 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2655, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2669 = destruct_comp c in
        match uu____2669 with
        | (u,uu____2674,wp) ->
            let uu____2676 =
              let uu____2682 =
                let uu____2683 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2683 in
              [uu____2682] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2676;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2693 =
          let uu____2697 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2698 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2697 uu____2698 in
        match uu____2693 with | (m,uu____2700,uu____2701) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2711 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2711
        then FStar_Syntax_Const.effect_Tot_lid
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
        let uu____2736 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2736 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2758 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2758 with
             | (a,kwp) ->
                 let uu____2775 = destruct_comp m1 in
                 let uu____2779 = destruct_comp m2 in
                 ((md, a, kwp), uu____2775, uu____2779))
let is_pure_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid
let is_pure_or_ghost_effect:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l in
      (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid)
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
            let uu____2827 =
              let uu____2828 =
                let uu____2834 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2834] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2828;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2827
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
          if FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid
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
      let uu___128_2870 = lc in
      let uu____2871 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___128_2870.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2871;
        FStar_Syntax_Syntax.cflags =
          (uu___128_2870.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2874  ->
             let uu____2875 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2875)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2879 =
      let uu____2880 = FStar_Syntax_Subst.compress t in
      uu____2880.FStar_Syntax_Syntax.n in
    match uu____2879 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2883 -> true
    | uu____2891 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2903 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2903
        then c
        else
          (let uu____2905 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2905
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2935 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2935] in
                       let us =
                         let uu____2938 =
                           let uu____2940 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2940] in
                         u_res :: uu____2938 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2951 =
                         let uu____2952 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2953 =
                           let uu____2954 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2955 =
                             let uu____2957 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2958 =
                               let uu____2960 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2960] in
                             uu____2957 :: uu____2958 in
                           uu____2954 :: uu____2955 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2952 uu____2953 in
                       uu____2951 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2966 = destruct_comp c1 in
              match uu____2966 with
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
        let close1 uu____2989 =
          let uu____2990 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2990 in
        let uu___129_2991 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_2991.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_2991.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___129_2991.FStar_Syntax_Syntax.cflags);
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
          let uu____3002 =
            let uu____3003 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____3003 in
          if uu____3002
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____3008 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____3008
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____3010 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____3010 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____3016 =
                        let uu____3017 =
                          let uu____3018 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3019 =
                            let uu____3020 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3021 =
                              let uu____3023 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3023] in
                            uu____3020 :: uu____3021 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3018 uu____3019 in
                        uu____3017
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____3016) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3029 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3029
         then
           let uu____3030 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3031 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3032 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3030
             uu____3031 uu____3032
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
          fun uu____3049  ->
            match uu____3049 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3059 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3059
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____3062 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____3064 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3065 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3062 uu____3064 bstr uu____3065
                  else ());
                 (let bind_it uu____3070 =
                    let uu____3071 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3071
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3081 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3081
                        then
                          let uu____3082 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____3084 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3085 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3086 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3087 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3082 uu____3084 uu____3085 uu____3086
                            uu____3087
                        else ());
                       (let try_simplify uu____3098 =
                          let aux uu____3108 =
                            let uu____3109 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3109
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____3128 ->
                                  let uu____3129 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3129
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3148 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3148
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____3184 =
                                  let uu____3187 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3187, reason) in
                                FStar_Util.Inl uu____3184
                            | uu____3190 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3205 =
                              let uu____3206 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3206.FStar_Syntax_Syntax.n in
                            match uu____3205 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3210) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3216 -> c in
                          let uu____3217 =
                            let uu____3218 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3218 in
                          if uu____3217
                          then
                            let uu____3226 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3226
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3240 =
                                  let uu____3241 =
                                    let uu____3244 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3244) in
                                  FStar_Errors.Error uu____3241 in
                                raise uu____3240))
                          else
                            (let uu____3252 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3252
                             then subst_c2 "both total"
                             else
                               (let uu____3260 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3260
                                then
                                  let uu____3267 =
                                    let uu____3270 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3270, "both gtot") in
                                  FStar_Util.Inl uu____3267
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____3286 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3287 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3287) in
                                       if uu____3286
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___130_3296 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___130_3296.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___130_3296.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3297 =
                                           let uu____3300 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3300, "c1 Tot") in
                                         FStar_Util.Inl uu____3297
                                       else aux ()
                                   | uu____3304 -> aux ()))) in
                        let uu____3309 = try_simplify () in
                        match uu____3309 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3327 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3327
                              then
                                let uu____3328 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3329 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3330 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3328 uu____3329 uu____3330
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3337 = lift_and_destruct env c1 c2 in
                            (match uu____3337 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3371 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3371]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____3373 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3373] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr
                                           (FStar_Syntax_Const.effect_Tot_lid,
                                             [FStar_Syntax_Syntax.TOTAL]))) in
                                 let r11 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_range r1))
                                     FStar_Pervasives_Native.None r1 in
                                 let wp_args =
                                   let uu____3396 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3397 =
                                     let uu____3399 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3400 =
                                       let uu____3402 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3403 =
                                         let uu____3405 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3406 =
                                           let uu____3408 =
                                             let uu____3409 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3409 in
                                           [uu____3408] in
                                         uu____3405 :: uu____3406 in
                                       uu____3402 :: uu____3403 in
                                     uu____3399 :: uu____3400 in
                                   uu____3396 :: uu____3397 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3414 =
                                     let uu____3415 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3415
                                       wp_args in
                                   uu____3414 FStar_Pervasives_Native.None
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
              let uu____3459 =
                let uu____3460 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3460 in
              if uu____3459
              then f
              else (let uu____3462 = reason1 () in label uu____3462 r f)
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
            let uu___131_3473 = g in
            let uu____3474 =
              let uu____3475 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3475 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3474;
              FStar_TypeChecker_Env.deferred =
                (uu___131_3473.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_3473.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_3473.FStar_TypeChecker_Env.implicits)
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
      | uu____3487 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3504 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3508 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3508
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3515 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3515
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3520 = destruct_comp c1 in
                    match uu____3520 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3533 =
                            let uu____3534 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3535 =
                              let uu____3536 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3537 =
                                let uu____3539 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3540 =
                                  let uu____3542 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3542] in
                                uu____3539 :: uu____3540 in
                              uu____3536 :: uu____3537 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3534
                              uu____3535 in
                          uu____3533 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___132_3547 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_3547.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_3547.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_3547.FStar_Syntax_Syntax.cflags);
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
            let uu____3574 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3574
            then (lc, g0)
            else
              ((let uu____3579 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3579
                then
                  let uu____3580 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3581 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3580 uu____3581
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3587  ->
                          match uu___98_3587 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3589 -> [])) in
                let strengthen uu____3595 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3603 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3603 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3610 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3611 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3611) in
                           if uu____3610
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3618 =
                                 let uu____3619 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3619 in
                               FStar_Syntax_Util.comp_set_flags uu____3618
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3624 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3624
                           then
                             let uu____3625 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3626 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3625 uu____3626
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3629 = destruct_comp c2 in
                           match uu____3629 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3642 =
                                   let uu____3643 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3644 =
                                     let uu____3645 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3646 =
                                       let uu____3648 =
                                         let uu____3649 =
                                           let uu____3650 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3650 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3649 in
                                       let uu____3651 =
                                         let uu____3653 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3653] in
                                       uu____3648 :: uu____3651 in
                                     uu____3645 :: uu____3646 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3643
                                     uu____3644 in
                                 uu____3642 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3659 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3659
                                 then
                                   let uu____3660 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3660
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3663 =
                  let uu___133_3664 = lc in
                  let uu____3665 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3666 =
                    let uu____3668 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3669 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3669) in
                    if uu____3668 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3665;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___133_3664.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3666;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3663,
                  (let uu___134_3672 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___134_3672.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___134_3672.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___134_3672.FStar_TypeChecker_Env.implicits)
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
            FStar_Syntax_Const.effect_PURE_lid in
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let y = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____3687 =
          let uu____3690 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3691 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3690, uu____3691) in
        match uu____3687 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3700 =
                let uu____3701 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3702 =
                  let uu____3703 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3704 =
                    let uu____3706 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3706] in
                  uu____3703 :: uu____3704 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3701 uu____3702 in
              uu____3700 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3714 =
                let uu____3715 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3716 =
                  let uu____3717 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3718 =
                    let uu____3720 =
                      let uu____3721 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3721 in
                    let uu____3722 =
                      let uu____3724 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3724] in
                    uu____3720 :: uu____3722 in
                  uu____3717 :: uu____3718 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3715 uu____3716 in
              uu____3714 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3732 =
                let uu____3733 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3734 =
                  let uu____3735 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3736 =
                    let uu____3738 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3739 =
                      let uu____3741 =
                        let uu____3742 =
                          let uu____3743 =
                            let uu____3744 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3744] in
                          FStar_Syntax_Util.abs uu____3743 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3742 in
                      [uu____3741] in
                    uu____3738 :: uu____3739 in
                  uu____3735 :: uu____3736 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3733 uu____3734 in
              uu____3732 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3760 = FStar_TypeChecker_Env.get_range env in
              bind uu____3760 env FStar_Pervasives_Native.None
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
          let comp uu____3778 =
            let uu____3779 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3779
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3782 =
                 let uu____3795 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3796 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3795 uu____3796 in
               match uu____3782 with
               | ((md,uu____3798,uu____3799),(u_res_t,res_t,wp_then),
                  (uu____3803,uu____3804,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3833 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3834 =
                       let uu____3835 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3836 =
                         let uu____3837 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3838 =
                           let uu____3840 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3841 =
                             let uu____3843 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3844 =
                               let uu____3846 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3846] in
                             uu____3843 :: uu____3844 in
                           uu____3840 :: uu____3841 in
                         uu____3837 :: uu____3838 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3835 uu____3836 in
                     uu____3834 FStar_Pervasives_Native.None uu____3833 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3854 =
                     let uu____3855 = FStar_Options.split_cases () in
                     uu____3855 > (Prims.parse_int "0") in
                   if uu____3854
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3861 =
                          let uu____3862 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3863 =
                            let uu____3864 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3865 =
                              let uu____3867 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3867] in
                            uu____3864 :: uu____3865 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3862 uu____3863 in
                        uu____3861 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3872 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3872;
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
      let uu____3879 =
        let uu____3880 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3880 in
      FStar_Syntax_Syntax.fvar uu____3879 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3900  ->
                 match uu____3900 with
                 | (uu____3903,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3908 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3910 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3910
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3930 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3931 =
                 let uu____3932 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3933 =
                   let uu____3934 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3935 =
                     let uu____3937 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3938 =
                       let uu____3940 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3941 =
                         let uu____3943 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3943] in
                       uu____3940 :: uu____3941 in
                     uu____3937 :: uu____3938 in
                   uu____3934 :: uu____3935 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3932 uu____3933 in
               uu____3931 FStar_Pervasives_Native.None uu____3930 in
             let default_case =
               let post_k =
                 let uu____3952 =
                   let uu____3956 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3956] in
                 let uu____3957 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3952 uu____3957 in
               let kwp =
                 let uu____3963 =
                   let uu____3967 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3967] in
                 let uu____3968 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3963 uu____3968 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____3973 =
                   let uu____3974 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3974] in
                 let uu____3975 =
                   let uu____3976 =
                     let uu____3979 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3979 in
                   let uu____3980 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3976 uu____3980 in
                 FStar_Syntax_Util.abs uu____3973 uu____3975
                   (FStar_Pervasives_Native.Some
                      (FStar_Util.Inr
                         (FStar_Syntax_Const.effect_Tot_lid,
                           [FStar_Syntax_Syntax.TOTAL]))) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Syntax_Const.effect_PURE_lid in
               mk_comp md u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____3994  ->
                    fun celse  ->
                      match uu____3994 with
                      | (g,cthen) ->
                          let uu____4000 =
                            let uu____4013 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____4013 celse in
                          (match uu____4000 with
                           | ((md,uu____4015,uu____4016),(uu____4017,uu____4018,wp_then),
                              (uu____4020,uu____4021,wp_else)) ->
                               let uu____4032 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4032 []))
                 lcases default_case in
             let uu____4033 =
               let uu____4034 = FStar_Options.split_cases () in
               uu____4034 > (Prims.parse_int "0") in
             if uu____4033
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4038 = destruct_comp comp1 in
                match uu____4038 with
                | (uu____4042,uu____4043,wp) ->
                    let wp1 =
                      let uu____4048 =
                        let uu____4049 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4050 =
                          let uu____4051 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4052 =
                            let uu____4054 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4054] in
                          uu____4051 :: uu____4052 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4049 uu____4050 in
                      uu____4048 FStar_Pervasives_Native.None
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
          let uu____4070 =
            ((let uu____4071 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4071) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4072 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4072) in
          if uu____4070
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4080 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4084 =
            (let uu____4085 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4085) || env.FStar_TypeChecker_Env.lax in
          if uu____4084
          then c
          else
            (let uu____4089 = FStar_Syntax_Util.is_partial_return c in
             if uu____4089
             then c
             else
               (let uu____4093 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4093
                then
                  let uu____4096 =
                    let uu____4097 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4097 in
                  (if uu____4096
                   then
                     let uu____4100 =
                       let uu____4101 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4102 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4101 uu____4102 in
                     failwith uu____4100
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4107 =
                        let uu____4108 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4108 in
                      if uu____4107
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___135_4113 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___135_4113.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___135_4113.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___135_4113.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4124 =
                       let uu____4127 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4127
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4124 in
                   let eq1 =
                     let uu____4131 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4131 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4133 =
                     let uu____4134 =
                       let uu____4139 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____4139.FStar_Syntax_Syntax.comp in
                     uu____4134 () in
                   FStar_Syntax_Util.comp_set_flags uu____4133 flags))) in
        let uu___136_4141 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_4141.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_4141.FStar_Syntax_Syntax.res_typ);
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
          let uu____4160 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4160 with
          | FStar_Pervasives_Native.None  ->
              let uu____4165 =
                let uu____4166 =
                  let uu____4169 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4170 = FStar_TypeChecker_Env.get_range env in
                  (uu____4169, uu____4170) in
                FStar_Errors.Error uu____4166 in
              raise uu____4165
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
            let uu____4196 =
              let uu____4197 = FStar_Syntax_Subst.compress t2 in
              uu____4197.FStar_Syntax_Syntax.n in
            match uu____4196 with
            | FStar_Syntax_Syntax.Tm_type uu____4200 -> true
            | uu____4201 -> false in
          let uu____4202 =
            let uu____4203 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4203.FStar_Syntax_Syntax.n in
          match uu____4202 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4209 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____4216 =
                  let uu____4217 =
                    let uu____4218 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4218 in
                  (FStar_Pervasives_Native.None, uu____4217) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____4216 in
              let e1 =
                let uu____4227 =
                  let uu____4228 =
                    let uu____4229 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4229] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4228 in
                uu____4227
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4236 -> (e, lc)
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
              (let uu____4256 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4256 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4269 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4281 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4281, false)
            else
              (let uu____4285 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4285, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____4291) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___137_4294 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___137_4294.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___137_4294.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___137_4294.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____4298 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4298 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___138_4303 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___138_4303.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___138_4303.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___138_4303.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4306 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4306.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4306.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4306.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4312 =
                     let uu____4313 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4313
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4318 =
                          let uu____4319 = FStar_Syntax_Subst.compress f1 in
                          uu____4319.FStar_Syntax_Syntax.n in
                        match uu____4318 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4324,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4326;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4327;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4328;_},uu____4329)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4353 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___140_4353.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___140_4353.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___140_4353.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4354 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4359 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4359
                              then
                                let uu____4360 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4361 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4362 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4363 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4360 uu____4361 uu____4362 uu____4363
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4366 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4366 with
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
                                  let uu____4377 = destruct_comp ct in
                                  (match uu____4377 with
                                   | (u_t,uu____4384,uu____4385) ->
                                       let wp =
                                         let uu____4389 =
                                           let uu____4390 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4391 =
                                             let uu____4392 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4393 =
                                               let uu____4395 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4395] in
                                             uu____4392 :: uu____4393 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4390 uu____4391 in
                                         uu____4389
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4401 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4401 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4411 =
                                             let uu____4412 =
                                               let uu____4413 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4413] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4412 in
                                           uu____4411
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4419 =
                                         let uu____4422 =
                                           FStar_All.pipe_left
                                             (fun _0_29  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4433 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4434 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4422
                                           uu____4433 e cret uu____4434 in
                                       (match uu____4419 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___141_4440 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___141_4440.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___141_4440.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4442 =
                                                let uu____4443 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4443 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____4442
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4453 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4453
                                              then
                                                let uu____4454 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4454
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4460  ->
                             match uu___99_4460 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4462 -> [])) in
                   let lc1 =
                     let uu___142_4464 = lc in
                     let uu____4465 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4465;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___143_4467 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4467.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4467.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4467.FStar_TypeChecker_Env.implicits)
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
        let uu____4487 =
          let uu____4488 =
            let uu____4489 =
              let uu____4490 =
                let uu____4491 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4491 in
              [uu____4490] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4489 in
          uu____4488 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4487 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4500 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4500
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4511 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4520 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4537)::(ens,uu____4539)::uu____4540 ->
                    let uu____4562 =
                      let uu____4564 = norm req in
                      FStar_Pervasives_Native.Some uu____4564 in
                    let uu____4565 =
                      let uu____4566 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4566 in
                    (uu____4562, uu____4565)
                | uu____4568 ->
                    let uu____4574 =
                      let uu____4575 =
                        let uu____4578 =
                          let uu____4579 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4579 in
                        (uu____4578, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4575 in
                    raise uu____4574)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4589)::uu____4590 ->
                    let uu____4604 =
                      let uu____4607 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____4607 in
                    (match uu____4604 with
                     | (us_r,uu____4624) ->
                         let uu____4625 =
                           let uu____4628 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____4628 in
                         (match uu____4625 with
                          | (us_e,uu____4645) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4648 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4648
                                  us_r in
                              let as_ens =
                                let uu____4650 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4650
                                  us_e in
                              let req =
                                let uu____4654 =
                                  let uu____4655 =
                                    let uu____4656 =
                                      let uu____4663 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4663] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4656 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4655 in
                                uu____4654
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4679 =
                                  let uu____4680 =
                                    let uu____4681 =
                                      let uu____4688 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4688] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4681 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4680 in
                                uu____4679 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4701 =
                                let uu____4703 = norm req in
                                FStar_Pervasives_Native.Some uu____4703 in
                              let uu____4704 =
                                let uu____4705 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4705 in
                              (uu____4701, uu____4704)))
                | uu____4707 -> failwith "Impossible"))
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
      (let uu____4727 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4727
       then
         let uu____4728 = FStar_Syntax_Print.term_to_string tm in
         let uu____4729 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4728 uu____4729
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
        (let uu____4750 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4750
         then
           let uu____4751 = FStar_Syntax_Print.term_to_string tm in
           let uu____4752 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4751
             uu____4752
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4757 =
      let uu____4758 =
        let uu____4759 = FStar_Syntax_Subst.compress t in
        uu____4759.FStar_Syntax_Syntax.n in
      match uu____4758 with
      | FStar_Syntax_Syntax.Tm_app uu____4762 -> false
      | uu____4772 -> true in
    if uu____4757
    then t
    else
      (let uu____4774 = FStar_Syntax_Util.head_and_args t in
       match uu____4774 with
       | (head1,args) ->
           let uu____4800 =
             let uu____4801 =
               let uu____4802 = FStar_Syntax_Subst.compress head1 in
               uu____4802.FStar_Syntax_Syntax.n in
             match uu____4801 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4805 -> false in
           if uu____4800
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____4821 ->
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
             let uu____4849 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4849 with
             | (formals,uu____4858) ->
                 let n_implicits =
                   let uu____4870 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4907  ->
                             match uu____4907 with
                             | (uu____4911,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____4870 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4983 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4983 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4997 =
                     let uu____4998 =
                       let uu____5001 =
                         let uu____5002 = FStar_Util.string_of_int n_expected in
                         let uu____5006 = FStar_Syntax_Print.term_to_string e in
                         let uu____5007 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____5002 uu____5006 uu____5007 in
                       let uu____5011 = FStar_TypeChecker_Env.get_range env in
                       (uu____5001, uu____5011) in
                     FStar_Errors.Error uu____4998 in
                   raise uu____4997
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___100_5024 =
             match uu___100_5024 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5043 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5043 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_30,uu____5104) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5126,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5145 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5145 with
                           | (v1,uu____5166,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5176 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5176 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5225 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5225)))
                      | (uu____5239,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5263 =
                      let uu____5277 = inst_n_binders t in
                      aux [] uu____5277 bs1 in
                    (match uu____5263 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5315) -> (e, torig, guard)
                          | (uu____5331,[]) when
                              let uu____5347 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5347 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5348 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5367 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5382 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____5394 =
    let uu____5396 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5396
      (FStar_List.map
         (fun u  ->
            let uu____5406 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5406 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5394 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5418 = FStar_Util.set_is_empty x in
      if uu____5418
      then []
      else
        (let s =
           let uu____5423 =
             let uu____5425 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5425 in
           FStar_All.pipe_right uu____5423 FStar_Util.set_elements in
         (let uu____5430 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5430
          then
            let uu____5431 =
              let uu____5432 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5432 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5431
          else ());
         (let r =
            let uu____5440 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____5440 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5452 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5452
                     then
                       let uu____5453 =
                         let uu____5454 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5454 in
                       let uu____5456 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5457 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5453 uu____5456 uu____5457
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
        let uu____5475 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5475 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5502 =
  match uu___101_5502 with
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
        | ([],uu____5543) -> generalized_univ_names
        | (uu____5547,[]) -> explicit_univ_names
        | uu____5551 ->
            let uu____5556 =
              let uu____5557 =
                let uu____5560 =
                  let uu____5561 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5561 in
                (uu____5560, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5557 in
            raise uu____5556
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
      (let uu____5575 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5575
       then
         let uu____5576 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5576
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5582 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5582
        then
          let uu____5583 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5583
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5588 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5588))
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
      let uu____5618 =
        let uu____5619 =
          FStar_Util.for_all
            (fun uu____5624  ->
               match uu____5624 with
               | (uu____5629,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5619 in
      if uu____5618
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____5652 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5652
            then
              let uu____5653 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5653
            else ());
           (let c1 =
              let uu____5656 = FStar_TypeChecker_Env.should_verify env in
              if uu____5656
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5659 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5659
             then
               let uu____5660 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5660
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5694 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5694 FStar_Util.set_elements in
         let uu____5738 =
           let uu____5756 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5811  ->
                     match uu____5811 with
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
           FStar_All.pipe_right uu____5756 FStar_List.unzip in
         match uu____5738 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5973 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5973
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
                      (fun uu____6015  ->
                         match uu____6015 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6072  ->
                                       match uu____6072 with
                                       | (u,k) ->
                                           let uu____6092 =
                                             FStar_Unionfind.find u in
                                           (match uu____6092 with
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6103;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6104;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6105;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6111,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6113;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6114;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6115;_},uu____6116);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6117;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6118;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6119;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____6147 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6155 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6160 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6160 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6184 =
                                                         let uu____6186 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_31)
                                                           uu____6186 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6184 kres in
                                                     let t =
                                                       let uu____6189 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6190 =
                                                         let uu____6197 =
                                                           let uu____6203 =
                                                             let uu____6204 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6204 in
                                                           FStar_Util.Inl
                                                             uu____6203 in
                                                         FStar_Pervasives_Native.Some
                                                           uu____6197 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6189
                                                         uu____6190 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6219 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6237 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6237, c)
                               | ([],uu____6238) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (e1, c1)
                               | uu____6250 ->
                                   let uu____6258 = (e, c) in
                                   (match uu____6258 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e in
                                        let t =
                                          let uu____6270 =
                                            let uu____6271 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6271.FStar_Syntax_Syntax.n in
                                          match uu____6270 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6288 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6288 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6298 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6308 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6308)) in
                             (match uu____6219 with
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
      (let uu____6346 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6346
       then
         let uu____6347 =
           let uu____6348 =
             FStar_List.map
               (fun uu____6353  ->
                  match uu____6353 with
                  | (lb,uu____6358,uu____6359) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6348 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6347
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6369  ->
              match uu____6369 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6384 =
           let uu____6391 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6407  ->
                     match uu____6407 with | (uu____6413,e,c) -> (e, c))) in
           gen env uu____6391 in
         match uu____6384 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6445  ->
                     match uu____6445 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____6489  ->
                  fun uu____6490  ->
                    match (uu____6489, uu____6490) with
                    | ((l,uu____6523,uu____6524),(us,e,c)) ->
                        ((let uu____6550 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6550
                          then
                            let uu____6551 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6552 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6553 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6554 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6551 uu____6552 uu____6553 uu____6554
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6573  ->
              match uu____6573 with
              | (l,generalized_univs,t,c) ->
                  let uu____6591 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6591, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6624 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6624 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____6628 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                     uu____6628) in
          let is_var e1 =
            let uu____6634 =
              let uu____6635 = FStar_Syntax_Subst.compress e1 in
              uu____6635.FStar_Syntax_Syntax.n in
            match uu____6634 with
            | FStar_Syntax_Syntax.Tm_name uu____6638 -> true
            | uu____6639 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___144_6657 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_6657.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_6657.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6658 ->
                let uu___145_6659 = e2 in
                let uu____6660 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6659.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6660;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6659.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6659.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___146_6669 = env1 in
            let uu____6670 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6669.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6669.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6669.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6669.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6669.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6669.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6669.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6669.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6669.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6669.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6669.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6669.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6669.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6669.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6669.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6670;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6669.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6669.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6669.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6669.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6669.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6669.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6669.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6669.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6671 = check env2 t1 t2 in
          match uu____6671 with
          | FStar_Pervasives_Native.None  ->
              let uu____6675 =
                let uu____6676 =
                  let uu____6679 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6680 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6679, uu____6680) in
                FStar_Errors.Error uu____6676 in
              raise uu____6675
          | FStar_Pervasives_Native.Some g ->
              ((let uu____6685 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6685
                then
                  let uu____6686 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6686
                else ());
               (let uu____6688 = decorate e t2 in (uu____6688, g)))
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
        let uu____6712 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6712
        then
          let uu____6715 = discharge g1 in
          let uu____6716 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6715, uu____6716)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6728 =
               let uu____6729 =
                 let uu____6730 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6730 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6729
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6728
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6732 = destruct_comp c1 in
           match uu____6732 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6744 = FStar_TypeChecker_Env.get_range env in
                 let uu____6745 =
                   let uu____6746 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6747 =
                     let uu____6748 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6749 =
                       let uu____6751 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6751] in
                     uu____6748 :: uu____6749 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6746 uu____6747 in
                 uu____6745
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6744 in
               ((let uu____6757 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6757
                 then
                   let uu____6758 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6758
                 else ());
                (let g2 =
                   let uu____6761 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6761 in
                 let uu____6762 = discharge g2 in
                 let uu____6763 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6762, uu____6763))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6787 =
        match uu___102_6787 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6793)::[] -> f fst1
        | uu____6806 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6811 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6811
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____6820 =
          let uu____6823 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6823 in
        FStar_All.pipe_right uu____6820
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____6834 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6834
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_6848 =
        match uu___103_6848 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6854)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6869)::[] ->
            let uu____6890 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6890
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____6895 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6902 =
          let uu____6907 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6907) in
        let uu____6912 =
          let uu____6918 =
            let uu____6923 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6923) in
          let uu____6928 =
            let uu____6934 =
              let uu____6939 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6939) in
            let uu____6944 =
              let uu____6950 =
                let uu____6955 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6955) in
              let uu____6960 =
                let uu____6966 =
                  let uu____6971 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6971) in
                [uu____6966; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6950 :: uu____6960 in
            uu____6934 :: uu____6944 in
          uu____6918 :: uu____6928 in
        uu____6902 :: uu____6912 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7012 =
            FStar_Util.find_map table
              (fun uu____7018  ->
                 match uu____7018 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____7031 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____7031
                     else FStar_Pervasives_Native.None) in
          (match uu____7012 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____7034 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7038 =
      let uu____7039 = FStar_Syntax_Util.un_uinst l in
      uu____7039.FStar_Syntax_Syntax.n in
    match uu____7038 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____7043 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7061)::uu____7062 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7068 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7072,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____7073))::uu____7074 -> bs
      | uu____7083 ->
          let uu____7084 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7084 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____7087 =
                 let uu____7088 = FStar_Syntax_Subst.compress t in
                 uu____7088.FStar_Syntax_Syntax.n in
               (match uu____7087 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7092) ->
                    let uu____7103 =
                      FStar_Util.prefix_until
                        (fun uu___104_7122  ->
                           match uu___104_7122 with
                           | (uu____7126,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7127)) ->
                               false
                           | uu____7129 -> true) bs' in
                    (match uu____7103 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____7147,uu____7148) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____7185,uu____7186) ->
                         let uu____7223 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7231  ->
                                   match uu____7231 with
                                   | (x,uu____7236) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7223
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7259  ->
                                     match uu____7259 with
                                     | (x,i) ->
                                         let uu____7270 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7270, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7276 -> bs))
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
              (let uu____7295 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7295 e.FStar_Syntax_Syntax.pos)
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
          let uu____7317 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7317
          then e
          else
            (let uu____7319 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7319
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
        (let uu____7345 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7345
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7347 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7347))
         else ());
        (let fv =
           let uu____7350 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7350
             FStar_Pervasives_Native.None in
         let lbname = FStar_Util.Inr fv in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def
              }]) in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident], [])) in
         let uu____7357 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___147_7366 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_7366.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_7366.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_7366.FStar_Syntax_Syntax.sigmeta)
           }), uu____7357))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7376 =
        match uu___105_7376 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7377 -> false in
      let reducibility uu___106_7381 =
        match uu___106_7381 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7382 -> false in
      let assumption uu___107_7386 =
        match uu___107_7386 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7387 -> false in
      let reification uu___108_7391 =
        match uu___108_7391 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7392 -> true
        | uu____7393 -> false in
      let inferred uu___109_7397 =
        match uu___109_7397 with
        | FStar_Syntax_Syntax.Discriminator uu____7398 -> true
        | FStar_Syntax_Syntax.Projector uu____7399 -> true
        | FStar_Syntax_Syntax.RecordType uu____7402 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7407 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7412 -> false in
      let has_eq uu___110_7416 =
        match uu___110_7416 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7417 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7451 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7454 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7457 =
        let uu____7458 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7460  ->
                  match uu___111_7460 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7461 -> false)) in
        FStar_All.pipe_right uu____7458 Prims.op_Negation in
      if uu____7457
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7471 =
            let uu____7472 =
              let uu____7475 =
                let uu____7476 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7476 msg in
              (uu____7475, r) in
            FStar_Errors.Error uu____7472 in
          raise uu____7471 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7484 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7492 =
            let uu____7493 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7493 in
          if uu____7492 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7497),uu____7498,uu____7499) ->
              ((let uu____7510 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7510
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7513 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7513
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7517 ->
              let uu____7522 =
                let uu____7523 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7523 in
              if uu____7522 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7527 ->
              let uu____7531 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7531 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7534 ->
              let uu____7537 =
                let uu____7538 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7538 in
              if uu____7537 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7542 ->
              let uu____7543 =
                let uu____7544 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7544 in
              if uu____7543 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7548 ->
              let uu____7549 =
                let uu____7550 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7550 in
              if uu____7549 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7554 ->
              let uu____7561 =
                let uu____7562 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7562 in
              if uu____7561 then err'1 () else ()
          | uu____7566 -> ()))
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
                          let uu____7623 =
                            let uu____7626 =
                              let uu____7627 =
                                let uu____7632 =
                                  let uu____7633 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7633 in
                                (uu____7632, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7627 in
                            FStar_Syntax_Syntax.mk uu____7626 in
                          uu____7623 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7659  ->
                                  match uu____7659 with
                                  | (x,imp) ->
                                      let uu____7666 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7666, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7670 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7670 in
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
                             let uu____7679 =
                               let uu____7680 =
                                 let uu____7681 =
                                   let uu____7682 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7683 =
                                     let uu____7684 =
                                       let uu____7685 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7685 in
                                     [uu____7684] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7682
                                     uu____7683 in
                                 uu____7681 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7680 in
                             FStar_Syntax_Util.refine x uu____7679 in
                           let uu____7690 =
                             let uu___148_7691 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_7691.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_7691.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7690) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7701 =
                          FStar_List.map
                            (fun uu____7711  ->
                               match uu____7711 with
                               | (x,uu____7718) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7701 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7742  ->
                                match uu____7742 with
                                | (x,uu____7749) ->
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
                             (let uu____7758 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____7758)
                               ||
                               (let uu____7759 =
                                  let uu____7760 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7760.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7759) in
                           let quals =
                             let uu____7763 =
                               let uu____7765 =
                                 let uu____7767 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7767
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7770 =
                                 FStar_List.filter
                                   (fun uu___112_7772  ->
                                      match uu___112_7772 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7773 -> false) iquals in
                               FStar_List.append uu____7765 uu____7770 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7763 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7786 =
                                 let uu____7787 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7787 in
                               FStar_Syntax_Syntax.mk_Total uu____7786 in
                             let uu____7788 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7788 in
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
                           (let uu____7791 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7791
                            then
                              let uu____7792 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7792
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
                                             fun uu____7824  ->
                                               match uu____7824 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7840 =
                                                       let uu____7843 =
                                                         let uu____7844 =
                                                           let uu____7849 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7849,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7844 in
                                                       pos uu____7843 in
                                                     (uu____7840, b)
                                                   else
                                                     (let uu____7853 =
                                                        let uu____7856 =
                                                          let uu____7857 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7857 in
                                                        pos uu____7856 in
                                                      (uu____7853, b)))) in
                                   let pat_true =
                                     let uu____7871 =
                                       let uu____7874 =
                                         let uu____7875 =
                                           let uu____7883 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____7883, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7875 in
                                       pos uu____7874 in
                                     (uu____7871,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____7909 =
                                       let uu____7912 =
                                         let uu____7913 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7913 in
                                       pos uu____7912 in
                                     (uu____7909,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____7924 =
                                     let uu____7927 =
                                       let uu____7928 =
                                         let uu____7944 =
                                           let uu____7946 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7947 =
                                             let uu____7949 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7949] in
                                           uu____7946 :: uu____7947 in
                                         (arg_exp, uu____7944) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7928 in
                                     FStar_Syntax_Syntax.mk uu____7927 in
                                   uu____7924 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____7960 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7960
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
                                let uu____7972 =
                                  let uu____7975 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____7975 in
                                let uu____7976 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7972;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7976
                                } in
                              let impl =
                                let uu____7980 =
                                  let uu____7981 =
                                    let uu____7987 =
                                      let uu____7989 =
                                        let uu____7990 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7990
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7989] in
                                    ((false, [lb]), uu____7987, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7981 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7980;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____8005 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8005
                               then
                                 let uu____8006 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8006
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
                                fun uu____8026  ->
                                  match uu____8026 with
                                  | (a,uu____8030) ->
                                      let uu____8031 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8031 with
                                       | (field_name,uu____8035) ->
                                           let field_proj_tm =
                                             let uu____8037 =
                                               let uu____8038 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8038 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8037 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8052 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8061  ->
                                    match uu____8061 with
                                    | (x,uu____8066) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8068 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8068 with
                                         | (field_name,uu____8073) ->
                                             let t =
                                               let uu____8075 =
                                                 let uu____8076 =
                                                   let uu____8079 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8079 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8076 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8075 in
                                             let only_decl =
                                               ((let uu____8081 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Parser_Const.prims_lid
                                                   uu____8081)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8082 =
                                                    let uu____8083 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8083.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8082) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8093 =
                                                   FStar_List.filter
                                                     (fun uu___113_8095  ->
                                                        match uu___113_8095
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8096 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8093
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_8104  ->
                                                         match uu___114_8104
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8105 ->
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
                                             ((let uu____8108 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8108
                                               then
                                                 let uu____8109 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8109
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
                                                           fun uu____8136  ->
                                                             match uu____8136
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8152
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8152,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8164
                                                                    =
                                                                    let uu____8167
                                                                    =
                                                                    let uu____8168
                                                                    =
                                                                    let uu____8173
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8173,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8168 in
                                                                    pos
                                                                    uu____8167 in
                                                                    (uu____8164,
                                                                    b))
                                                                   else
                                                                    (let uu____8177
                                                                    =
                                                                    let uu____8180
                                                                    =
                                                                    let uu____8181
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8181 in
                                                                    pos
                                                                    uu____8180 in
                                                                    (uu____8177,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8193 =
                                                     let uu____8196 =
                                                       let uu____8197 =
                                                         let uu____8205 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8205,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8197 in
                                                     pos uu____8196 in
                                                   let uu____8211 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8193,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8211) in
                                                 let body =
                                                   let uu____8222 =
                                                     let uu____8225 =
                                                       let uu____8226 =
                                                         let uu____8242 =
                                                           let uu____8244 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8244] in
                                                         (arg_exp,
                                                           uu____8242) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8226 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8225 in
                                                   uu____8222
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8261 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8261
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
                                                   let uu____8267 =
                                                     let uu____8270 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8270 in
                                                   let uu____8271 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8267;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8271
                                                   } in
                                                 let impl =
                                                   let uu____8275 =
                                                     let uu____8276 =
                                                       let uu____8282 =
                                                         let uu____8284 =
                                                           let uu____8285 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8285
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8284] in
                                                       ((false, [lb]),
                                                         uu____8282, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8276 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8275;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8300 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8300
                                                  then
                                                    let uu____8301 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8301
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8052 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8331) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____8334 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8334 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8347 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8347 with
                    | (formals,uu____8357) ->
                        let uu____8368 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8381 =
                                   let uu____8382 =
                                     let uu____8383 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8383 in
                                   FStar_Ident.lid_equals typ_lid uu____8382 in
                                 if uu____8381
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8393,uvs',tps,typ0,uu____8397,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8410 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Syntax_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____8368 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8452 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8452 with
                              | (indices,uu____8462) ->
                                  let refine_domain =
                                    let uu____8474 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8476  ->
                                              match uu___115_8476 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8477 -> true
                                              | uu____8482 -> false)) in
                                    if uu____8474
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8489 =
                                      match uu___116_8489 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8491,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8498 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8499 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8499 with
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
                                    let uu____8507 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8507 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8538  ->
                                               fun uu____8539  ->
                                                 match (uu____8538,
                                                         uu____8539)
                                                 with
                                                 | ((x,uu____8549),(x',uu____8551))
                                                     ->
                                                     let uu____8556 =
                                                       let uu____8561 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8561) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8556) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8562 -> []