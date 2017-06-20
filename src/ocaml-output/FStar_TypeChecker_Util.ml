open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv option* FStar_Syntax_Syntax.lcomp)
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
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let uu____33 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____33
      (FStar_List.filter
         (fun uu____39  ->
            match uu____39 with
            | (x,uu____43) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____55 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____56 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____56) in
        if uu____55
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____58 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____58 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  = fun env  -> fun k  -> let uu____67 = new_uvar_aux env k in fst uu____67
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___99_73  ->
    match uu___99_73 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____75);
        FStar_Syntax_Syntax.tk = uu____76;
        FStar_Syntax_Syntax.pos = uu____77;
        FStar_Syntax_Syntax.vars = uu____78;_} -> uv
    | uu____93 -> failwith "Impossible"
let new_implicit_var:
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* (FStar_Syntax_Syntax.uvar*
            FStar_Range.range) Prims.list* FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____116 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____116 with
          | Some (uu____129::(tm,uu____131)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____171 ->
              let uu____178 = new_uvar_aux env k in
              (match uu____178 with
               | (t,u) ->
                   let g =
                     let uu___119_190 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____191 =
                       let uu____199 =
                         let uu____206 = as_uvar u in
                         (reason, env, uu____206, t, k, r) in
                       [uu____199] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_190.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_190.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_190.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____191
                     } in
                   let uu____219 =
                     let uu____223 =
                       let uu____226 = as_uvar u in (uu____226, r) in
                     [uu____223] in
                   (t, uu____219, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____246 =
        let uu____247 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____247 in
      if uu____246
      then
        let us =
          let uu____251 =
            let uu____253 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____261  ->
                 match uu____261 with
                 | (x,uu____265) -> FStar_Syntax_Print.uvar_to_string x)
              uu____253 in
          FStar_All.pipe_right uu____251 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____271 =
            let uu____272 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____272 in
          FStar_Errors.err r uu____271);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____282 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____282 with
    | None  ->
        let uu____287 =
          let uu____288 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____289 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____288 uu____289 in
        failwith uu____287
    | Some tk -> tk
let force_sort s =
  let uu____306 =
    let uu____309 = force_sort' s in FStar_Syntax_Syntax.mk uu____309 in
  uu____306 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____328  ->
      match uu____328 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____335;
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
                   let uu____367 =
                     let uu____368 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____368.FStar_Syntax_Syntax.n in
                   match uu____367 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____373 = FStar_Syntax_Util.type_u () in
                       (match uu____373 with
                        | (k,uu____379) ->
                            let t2 =
                              let uu____381 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____381
                                FStar_Pervasives.fst in
                            ((let uu___120_386 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_386.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_386.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____387 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____412) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____419) ->
                       ((fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____465) ->
                       let uu____478 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____502  ->
                                 fun uu____503  ->
                                   match (uu____502, uu____503) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____545 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____545 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____478 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____606 = aux must_check_ty1 scope body in
                            (match uu____606 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____623 =
                                         FStar_Options.ml_ish () in
                                       if uu____623
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____630 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____630
                                   then
                                     let uu____631 =
                                       FStar_Range.string_of_range r in
                                     let uu____632 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____633 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____631 uu____632 uu____633
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____641 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____649 =
                            let uu____652 =
                              let uu____653 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____653
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____652 in
                          (uu____649, false)) in
                 let uu____660 =
                   let uu____665 = t_binders env in aux false uu____665 e in
                 match uu____660 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____682 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____682
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____686 =
                                let uu____687 =
                                  let uu____690 =
                                    let uu____691 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____691 in
                                  (uu____690, rng) in
                                FStar_Errors.Error uu____687 in
                              raise uu____686)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____698 ->
               let uu____699 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____699 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
let pat_as_exp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term*
          FStar_Syntax_Syntax.pat)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  None p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____783) ->
              let uu____788 = FStar_Syntax_Util.type_u () in
              (match uu____788 with
               | (k,uu____801) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_804 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_804.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_804.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____805 =
                     let uu____808 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____808 t in
                   (match uu____805 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_823 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___122_823.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___122_823.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____830 = FStar_Syntax_Util.type_u () in
              (match uu____830 with
               | (t,uu____843) ->
                   let x1 =
                     let uu___123_845 = x in
                     let uu____846 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_845.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_845.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____846
                     } in
                   let env2 =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env1 x1
                     else env1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [], [x1], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____868 = FStar_Syntax_Util.type_u () in
              (match uu____868 with
               | (t,uu____881) ->
                   let x1 =
                     let uu___124_883 = x in
                     let uu____884 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_883.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_883.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____884
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____916 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____972  ->
                        fun uu____973  ->
                          match (uu____972, uu____973) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1072 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1072 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____916 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1180 =
                       let uu____1183 =
                         let uu____1184 =
                           let uu____1189 =
                             let uu____1192 =
                               let uu____1193 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1194 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1193
                                 uu____1194 in
                             uu____1192 None p1.FStar_Syntax_Syntax.p in
                           (uu____1189,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1184 in
                       FStar_Syntax_Syntax.mk uu____1183 in
                     uu____1180 None p1.FStar_Syntax_Syntax.p in
                   let uu____1211 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1217 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1223 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1211, uu____1217, uu____1223, env2, e,
                     (let uu___125_1236 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___125_1236.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___125_1236.FStar_Syntax_Syntax.p)
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
                  (fun uu____1298  ->
                     match uu____1298 with
                     | (p2,imp) ->
                         let uu____1313 = elaborate_pat env1 p2 in
                         (uu____1313, imp)) pats in
              let uu____1318 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1318 with
               | (uu____1327,t) ->
                   let uu____1329 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1329 with
                    | (f,uu____1340) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1415::uu____1416) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1451::uu____1452,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1492  ->
                                      match uu____1492 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1510 =
                                                   let uu____1512 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1512 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1510
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1518 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1518, true)
                                           | uu____1523 ->
                                               let uu____1525 =
                                                 let uu____1526 =
                                                   let uu____1529 =
                                                     let uu____1530 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1530 in
                                                   (uu____1529,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1526 in
                                               raise uu____1525)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1581,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1582))
                                   when p_imp ->
                                   let uu____1584 = aux formals' pats' in
                                   (p2, true) :: uu____1584
                               | (uu____1596,Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (Some (p2.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun in
                                   let p3 =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                   let uu____1607 = aux formals' pats2 in
                                   (p3, true) :: uu____1607
                               | (uu____1619,imp) ->
                                   let uu____1623 =
                                     let uu____1628 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1628) in
                                   let uu____1631 = aux formals' pats' in
                                   uu____1623 :: uu____1631) in
                        let uu___126_1641 = p1 in
                        let uu____1644 =
                          let uu____1645 =
                            let uu____1653 = aux f pats1 in (fv, uu____1653) in
                          FStar_Syntax_Syntax.Pat_cons uu____1645 in
                        {
                          FStar_Syntax_Syntax.v = uu____1644;
                          FStar_Syntax_Syntax.ty =
                            (uu___126_1641.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___126_1641.FStar_Syntax_Syntax.p)
                        }))
          | uu____1664 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1690 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1690 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1720 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1720 with
               | Some x ->
                   let uu____1733 =
                     let uu____1734 =
                       let uu____1737 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1737, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1734 in
                   raise uu____1733
               | uu____1746 -> (b, a, w, arg, p3)) in
        let uu____1751 = one_pat true env p in
        match uu____1751 with
        | (b,uu____1765,uu____1766,tm,p1) -> (b, tm, p1)
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
          | (uu____1810,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1812)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1817,FStar_Syntax_Syntax.Tm_constant uu____1818) ->
              let uu____1819 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1819
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1823 =
                    let uu____1824 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1825 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1824 uu____1825 in
                  failwith uu____1823)
               else ();
               (let uu____1828 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1828
                then
                  let uu____1829 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1830 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1829
                    uu____1830
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_1834 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_1834.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_1834.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1838 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1838
                then
                  let uu____1839 =
                    let uu____1840 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1841 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1840 uu____1841 in
                  failwith uu____1839
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_1845 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1845.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1845.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1847),uu____1848) ->
              let s = force_sort e1 in
              let x1 =
                let uu___129_1857 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___129_1857.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___129_1857.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1870 =
                  let uu____1871 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1871 in
                if uu____1870
                then
                  let uu____1872 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1872
                else ());
               (let uu____1882 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1882))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1895;
                FStar_Syntax_Syntax.pos = uu____1896;
                FStar_Syntax_Syntax.vars = uu____1897;_},args))
              ->
              ((let uu____1924 =
                  let uu____1925 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1925 Prims.op_Negation in
                if uu____1924
                then
                  let uu____1926 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1926
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2014 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2014
                  | (arg::args2,(argpat,uu____2027)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2077) ->
                           let x =
                             let uu____2093 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2093 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2107) ->
                           let pat =
                             let uu____2122 = aux argpat e2 in
                             let uu____2123 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2122, uu____2123) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2126 ->
                      let uu____2140 =
                        let uu____2141 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2142 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2141 uu____2142 in
                      failwith uu____2140 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2152;
                     FStar_Syntax_Syntax.pos = uu____2153;
                     FStar_Syntax_Syntax.vars = uu____2154;_},uu____2155);
                FStar_Syntax_Syntax.tk = uu____2156;
                FStar_Syntax_Syntax.pos = uu____2157;
                FStar_Syntax_Syntax.vars = uu____2158;_},args))
              ->
              ((let uu____2189 =
                  let uu____2190 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2190 Prims.op_Negation in
                if uu____2189
                then
                  let uu____2191 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2191
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2279 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2279
                  | (arg::args2,(argpat,uu____2292)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2342) ->
                           let x =
                             let uu____2358 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2358 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2372) ->
                           let pat =
                             let uu____2387 = aux argpat e2 in
                             let uu____2388 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2387, uu____2388) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2391 ->
                      let uu____2405 =
                        let uu____2406 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2407 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2406 uu____2407 in
                      failwith uu____2405 in
                match_args [] args argpats))
          | uu____2414 ->
              let uu____2417 =
                let uu____2418 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2419 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2420 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2418 uu____2419 uu____2420 in
              failwith uu____2417 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2455 =
      match uu____2455 with
      | (p,i) ->
          let uu____2465 = decorated_pattern_as_term p in
          (match uu____2465 with
           | (vars,te) ->
               let uu____2478 =
                 let uu____2481 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2481) in
               (vars, uu____2478)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2489 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2489)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2492 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2492)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2495 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2495)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2509 =
          let uu____2517 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2517 FStar_List.unzip in
        (match uu____2509 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2575 =
               let uu____2576 =
                 let uu____2577 =
                   let uu____2587 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2587, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2577 in
               mk1 uu____2576 in
             (vars1, uu____2575))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____2617)::[] -> wp
      | uu____2630 ->
          let uu____2636 =
            let uu____2637 =
              let uu____2638 =
                FStar_List.map
                  (fun uu____2642  ->
                     match uu____2642 with
                     | (x,uu____2646) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2638 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2637 in
          failwith uu____2636 in
    let uu____2650 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2650, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2667 = destruct_comp c in
        match uu____2667 with
        | (u,uu____2672,wp) ->
            let uu____2674 =
              let uu____2680 =
                let uu____2681 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2681 in
              [uu____2680] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2674;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2694 =
          let uu____2698 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2699 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2698 uu____2699 in
        match uu____2694 with | (m,uu____2701,uu____2702) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2715 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2715
        then FStar_Syntax_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
let lift_and_destruct:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.bv*
          FStar_Syntax_Syntax.term)* (FStar_Syntax_Syntax.universe*
          FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)*
          (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.typ*
          FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1 in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2 in
        let uu____2743 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2743 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2765 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2765 with
             | (a,kwp) ->
                 let uu____2782 = destruct_comp m1 in
                 let uu____2786 = destruct_comp m2 in
                 ((md, a, kwp), uu____2782, uu____2786))
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
            let uu____2843 =
              let uu____2844 =
                let uu____2850 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2850] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2844;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2843
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
          then FStar_Syntax_Syntax.mk_Total' result (Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
let subst_lcomp:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst1  ->
    fun lc  ->
      let uu___130_2897 = lc in
      let uu____2898 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___130_2897.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2898;
        FStar_Syntax_Syntax.cflags =
          (uu___130_2897.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2901  ->
             let uu____2902 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2902)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2907 =
      let uu____2908 = FStar_Syntax_Subst.compress t in
      uu____2908.FStar_Syntax_Syntax.n in
    match uu____2907 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2911 -> true
    | uu____2919 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2934 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2934
        then c
        else
          (let uu____2936 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2936
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2966 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2966] in
                       let us =
                         let uu____2969 =
                           let uu____2971 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2971] in
                         u_res :: uu____2969 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Syntax_Const.effect_Tot_lid None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2975 =
                         let uu____2976 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2977 =
                           let uu____2978 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2979 =
                             let uu____2981 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2982 =
                               let uu____2984 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2984] in
                             uu____2981 :: uu____2982 in
                           uu____2978 :: uu____2979 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2976 uu____2977 in
                       uu____2975 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2990 = destruct_comp c1 in
              match uu____2990 with
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
        let close1 uu____3016 =
          let uu____3017 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____3017 in
        let uu___131_3018 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_3018.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_3018.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_3018.FStar_Syntax_Syntax.cflags);
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
          let uu____3032 =
            let uu____3033 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____3033 in
          if uu____3032
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____3038 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____3038
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____3040 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____3040 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____3046 =
                        let uu____3047 =
                          let uu____3048 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3049 =
                            let uu____3050 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3051 =
                              let uu____3053 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3053] in
                            uu____3050 :: uu____3051 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3048 uu____3049 in
                        uu____3047 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____3046) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3059 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3059
         then
           let uu____3060 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3061 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3062 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3060
             uu____3061 uu____3062
         else ());
        c
let bind:
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____3084  ->
            match uu____3084 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3094 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3094
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3097 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3099 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3100 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3097 uu____3099 bstr uu____3100
                  else ());
                 (let bind_it uu____3105 =
                    let uu____3106 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3106
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3116 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3116
                        then
                          let uu____3117 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3119 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3120 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3121 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3122 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3117 uu____3119 uu____3120 uu____3121
                            uu____3122
                        else ());
                       (let try_simplify uu____3133 =
                          let aux uu____3143 =
                            let uu____3144 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3144
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3163 ->
                                  let uu____3164 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3164
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3183 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3183
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3219 =
                                  let uu____3222 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3222, reason) in
                                FStar_Util.Inl uu____3219
                            | uu____3225 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3240 =
                              let uu____3241 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3241.FStar_Syntax_Syntax.n in
                            match uu____3240 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3245) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3251 -> c in
                          let uu____3252 =
                            let uu____3253 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3253 in
                          if uu____3252
                          then
                            let uu____3261 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3261
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3275 =
                                  let uu____3276 =
                                    let uu____3279 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3279) in
                                  FStar_Errors.Error uu____3276 in
                                raise uu____3275))
                          else
                            (let uu____3287 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3287
                             then subst_c2 "both total"
                             else
                               (let uu____3295 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3295
                                then
                                  let uu____3302 =
                                    let uu____3305 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3305, "both gtot") in
                                  FStar_Util.Inl uu____3302
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3321 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3322 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3322) in
                                       if uu____3321
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___132_3331 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___132_3331.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___132_3331.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3332 =
                                           let uu____3335 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3335, "c1 Tot") in
                                         FStar_Util.Inl uu____3332
                                       else aux ()
                                   | uu____3339 -> aux ()))) in
                        let uu____3344 = try_simplify () in
                        match uu____3344 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3362 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3362
                              then
                                let uu____3363 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3364 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3365 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3363 uu____3364 uu____3365
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3372 = lift_and_destruct env c1 c2 in
                            (match uu____3372 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3406 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3406]
                                   | Some x ->
                                       let uu____3408 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3408] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (Some
                                        (FStar_Syntax_Util.mk_residual_comp
                                           FStar_Syntax_Const.effect_Tot_lid
                                           None [FStar_Syntax_Syntax.TOTAL])) in
                                 let r11 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_range r1)) None r1 in
                                 let wp_args =
                                   let uu____3424 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3425 =
                                     let uu____3427 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3428 =
                                       let uu____3430 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3431 =
                                         let uu____3433 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3434 =
                                           let uu____3436 =
                                             let uu____3437 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3437 in
                                           [uu____3436] in
                                         uu____3433 :: uu____3434 in
                                       uu____3430 :: uu____3431 in
                                     uu____3427 :: uu____3428 in
                                   uu____3424 :: uu____3425 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3442 =
                                     let uu____3443 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3443
                                       wp_args in
                                   uu____3442 None t2.FStar_Syntax_Syntax.pos in
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
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false)))) None
          f.FStar_Syntax_Syntax.pos
let label_opt:
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | None  -> f
          | Some reason1 ->
              let uu____3494 =
                let uu____3495 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3495 in
              if uu____3494
              then f
              else (let uu____3497 = reason1 () in label uu____3497 r f)
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
            let uu___133_3511 = g in
            let uu____3512 =
              let uu____3513 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3513 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3512;
              FStar_TypeChecker_Env.deferred =
                (uu___133_3511.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_3511.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_3511.FStar_TypeChecker_Env.implicits)
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
      | uu____3525 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3545 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3549 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3549
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3556 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3556
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3561 = destruct_comp c1 in
                    match uu____3561 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3574 =
                            let uu____3575 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3576 =
                              let uu____3577 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3578 =
                                let uu____3580 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3581 =
                                  let uu____3583 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3583] in
                                uu____3580 :: uu____3581 in
                              uu____3577 :: uu____3578 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3575
                              uu____3576 in
                          uu____3574 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___134_3588 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___134_3588.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___134_3588.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___134_3588.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = weaken
        }
let strengthen_precondition:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp* FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun env  ->
      fun e  ->
        fun lc  ->
          fun g0  ->
            let uu____3620 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3620
            then (lc, g0)
            else
              ((let uu____3625 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3625
                then
                  let uu____3626 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3627 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3626 uu____3627
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3633  ->
                          match uu___100_3633 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3635 -> [])) in
                let strengthen uu____3641 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3649 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3649 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3656 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3657 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3657) in
                           if uu____3656
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3664 =
                                 let uu____3665 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3665 in
                               FStar_Syntax_Util.comp_set_flags uu____3664
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3670 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3670
                           then
                             let uu____3671 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3672 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3671 uu____3672
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3675 = destruct_comp c2 in
                           match uu____3675 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3688 =
                                   let uu____3689 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3690 =
                                     let uu____3691 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3692 =
                                       let uu____3694 =
                                         let uu____3695 =
                                           let uu____3696 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3696 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3695 in
                                       let uu____3697 =
                                         let uu____3699 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3699] in
                                       uu____3694 :: uu____3697 in
                                     uu____3691 :: uu____3692 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3689
                                     uu____3690 in
                                 uu____3688 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3705 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3705
                                 then
                                   let uu____3706 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3706
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3709 =
                  let uu___135_3710 = lc in
                  let uu____3711 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3712 =
                    let uu____3714 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3715 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3715) in
                    if uu____3714 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3711;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___135_3710.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3712;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3709,
                  (let uu___136_3718 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___136_3718.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___136_3718.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___136_3718.FStar_TypeChecker_Env.implicits)
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
        let x = FStar_Syntax_Syntax.new_bv None res_t in
        let y = FStar_Syntax_Syntax.new_bv None res_t in
        let uu____3736 =
          let uu____3739 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3740 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3739, uu____3740) in
        match uu____3736 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3749 =
                let uu____3750 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3751 =
                  let uu____3752 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3753 =
                    let uu____3755 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3755] in
                  uu____3752 :: uu____3753 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3750 uu____3751 in
              uu____3749 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3763 =
                let uu____3764 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3765 =
                  let uu____3766 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3767 =
                    let uu____3769 =
                      let uu____3770 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3770 in
                    let uu____3771 =
                      let uu____3773 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3773] in
                    uu____3769 :: uu____3771 in
                  uu____3766 :: uu____3767 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3764 uu____3765 in
              uu____3763 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3781 =
                let uu____3782 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3783 =
                  let uu____3784 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3785 =
                    let uu____3787 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3788 =
                      let uu____3790 =
                        let uu____3791 =
                          let uu____3792 =
                            let uu____3793 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3793] in
                          FStar_Syntax_Util.abs uu____3792 x_eq_y_yret
                            (Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Syntax_Const.effect_Tot_lid None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3791 in
                      [uu____3790] in
                    uu____3787 :: uu____3788 in
                  uu____3784 :: uu____3785 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3782 uu____3783 in
              uu____3781 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3802 = FStar_TypeChecker_Env.get_range env in
              bind uu____3802 env None (FStar_Syntax_Util.lcomp_of_comp comp)
                ((Some x), (FStar_Syntax_Util.lcomp_of_comp lc2)) in
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
          let comp uu____3824 =
            let uu____3825 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3825
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3828 =
                 let uu____3841 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3842 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3841 uu____3842 in
               match uu____3828 with
               | ((md,uu____3844,uu____3845),(u_res_t,res_t,wp_then),
                  (uu____3849,uu____3850,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3879 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3880 =
                       let uu____3881 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3882 =
                         let uu____3883 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3884 =
                           let uu____3886 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3887 =
                             let uu____3889 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3890 =
                               let uu____3892 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3892] in
                             uu____3889 :: uu____3890 in
                           uu____3886 :: uu____3887 in
                         uu____3883 :: uu____3884 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3881 uu____3882 in
                     uu____3880 None uu____3879 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3900 =
                     let uu____3901 = FStar_Options.split_cases () in
                     uu____3901 > (Prims.parse_int "0") in
                   if uu____3900
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3907 =
                          let uu____3908 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3909 =
                            let uu____3910 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3911 =
                              let uu____3913 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3913] in
                            uu____3910 :: uu____3911 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3908 uu____3909 in
                        uu____3907 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3918 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3918;
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
      let uu____3927 =
        let uu____3928 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3928 in
      FStar_Syntax_Syntax.fvar uu____3927 FStar_Syntax_Syntax.Delta_constant
        None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula* FStar_Syntax_Syntax.lcomp) Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____3951  ->
                 match uu____3951 with
                 | (uu____3954,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3959 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3961 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3961
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3981 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3982 =
                 let uu____3983 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3984 =
                   let uu____3985 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3986 =
                     let uu____3988 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3989 =
                       let uu____3991 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3992 =
                         let uu____3994 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3994] in
                       uu____3991 :: uu____3992 in
                     uu____3988 :: uu____3989 in
                   uu____3985 :: uu____3986 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3983 uu____3984 in
               uu____3982 None uu____3981 in
             let default_case =
               let post_k =
                 let uu____4003 =
                   let uu____4007 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____4007] in
                 let uu____4008 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4003 uu____4008 in
               let kwp =
                 let uu____4014 =
                   let uu____4018 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____4018] in
                 let uu____4019 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4014 uu____4019 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____4024 =
                   let uu____4025 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____4025] in
                 let uu____4026 =
                   let uu____4027 =
                     let uu____4030 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____4030 in
                   let uu____4031 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____4027 uu____4031 in
                 FStar_Syntax_Util.abs uu____4024 uu____4026
                   (Some
                      (FStar_Syntax_Util.mk_residual_comp
                         FStar_Syntax_Const.effect_Tot_lid None
                         [FStar_Syntax_Syntax.TOTAL])) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Syntax_Const.effect_PURE_lid in
               mk_comp md u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____4038  ->
                    fun celse  ->
                      match uu____4038 with
                      | (g,cthen) ->
                          let uu____4044 =
                            let uu____4057 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____4057 celse in
                          (match uu____4044 with
                           | ((md,uu____4059,uu____4060),(uu____4061,uu____4062,wp_then),
                              (uu____4064,uu____4065,wp_else)) ->
                               let uu____4076 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4076 []))
                 lcases default_case in
             let uu____4077 =
               let uu____4078 = FStar_Options.split_cases () in
               uu____4078 > (Prims.parse_int "0") in
             if uu____4077
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4082 = destruct_comp comp1 in
                match uu____4082 with
                | (uu____4086,uu____4087,wp) ->
                    let wp1 =
                      let uu____4092 =
                        let uu____4093 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4094 =
                          let uu____4095 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4096 =
                            let uu____4098 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4098] in
                          uu____4095 :: uu____4096 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4093 uu____4094 in
                      uu____4092 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4117 =
            ((let uu____4118 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4118) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4119 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4119) in
          if uu____4117
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4127 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4131 =
            (let uu____4132 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4132) || env.FStar_TypeChecker_Env.lax in
          if uu____4131
          then c
          else
            (let uu____4136 = FStar_Syntax_Util.is_partial_return c in
             if uu____4136
             then c
             else
               (let uu____4140 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4140
                then
                  let uu____4143 =
                    let uu____4144 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4144 in
                  (if uu____4143
                   then
                     let uu____4147 =
                       let uu____4148 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4149 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4148 uu____4149 in
                     failwith uu____4147
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4154 =
                        let uu____4155 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4155 in
                      if uu____4154
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___137_4160 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___137_4160.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___137_4160.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___137_4160.FStar_Syntax_Syntax.effect_args);
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
                       (Some (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret1 =
                     let uu____4171 =
                       let uu____4174 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4174
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4171 in
                   let eq1 =
                     let uu____4178 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4178 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4180 =
                     let uu____4181 =
                       let uu____4186 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4186.FStar_Syntax_Syntax.comp in
                     uu____4181 () in
                   FStar_Syntax_Util.comp_set_flags uu____4180 flags))) in
        let uu___138_4188 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___138_4188.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___138_4188.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = refine1
        }
let check_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____4211 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4211 with
          | None  ->
              let uu____4216 =
                let uu____4217 =
                  let uu____4220 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4221 = FStar_TypeChecker_Env.get_range env in
                  (uu____4220, uu____4221) in
                FStar_Errors.Error uu____4217 in
              raise uu____4216
          | Some g -> (e, c', g)
let maybe_coerce_bool_to_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
            let uu____4251 =
              let uu____4252 = FStar_Syntax_Subst.compress t2 in
              uu____4252.FStar_Syntax_Syntax.n in
            match uu____4251 with
            | FStar_Syntax_Syntax.Tm_type uu____4255 -> true
            | uu____4256 -> false in
          let uu____4257 =
            let uu____4258 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4258.FStar_Syntax_Syntax.n in
          match uu____4257 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4264 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4271 =
                  let uu____4272 =
                    let uu____4273 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4273 in
                  (None, uu____4272) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4271 in
              let e1 =
                let uu____4282 =
                  let uu____4283 =
                    let uu____4284 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4284] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4283 in
                uu____4282
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4291 -> (e, lc)
let weaken_result_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____4315 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4315 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4328 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4340 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4340, false)
            else
              (let uu____4344 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4344, true)) in
          match gopt with
          | (None ,uu____4350) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___139_4353 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___139_4353.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___139_4353.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___139_4353.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4357 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4357 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_4362 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_4362.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_4362.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___140_4362.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_4365 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_4365.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_4365.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_4365.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4371 =
                     let uu____4372 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4372
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____4377 =
                          let uu____4378 = FStar_Syntax_Subst.compress f1 in
                          uu____4378.FStar_Syntax_Syntax.n in
                        match uu____4377 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4383,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4385;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4386;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4387;_},uu____4388)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_4402 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_4402.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_4402.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___142_4402.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4403 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4408 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4408
                              then
                                let uu____4409 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4410 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4411 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4412 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4409 uu____4410 uu____4411 uu____4412
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4415 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4415 with
                              | (a,kwp) ->
                                  let k =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (a, t)] kwp in
                                  let md =
                                    FStar_TypeChecker_Env.get_effect_decl env
                                      ct.FStar_Syntax_Syntax.effect_name in
                                  let x =
                                    FStar_Syntax_Syntax.new_bv
                                      (Some (t.FStar_Syntax_Syntax.pos)) t in
                                  let xexp = FStar_Syntax_Syntax.bv_to_name x in
                                  let uu____4426 = destruct_comp ct in
                                  (match uu____4426 with
                                   | (u_t,uu____4433,uu____4434) ->
                                       let wp =
                                         let uu____4438 =
                                           let uu____4439 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4440 =
                                             let uu____4441 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4442 =
                                               let uu____4444 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4444] in
                                             uu____4441 :: uu____4442 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4439 uu____4440 in
                                         uu____4438
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4450 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4450 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4460 =
                                             let uu____4461 =
                                               let uu____4462 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4462] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4461 in
                                           uu____4460
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4468 =
                                         let uu____4471 =
                                           FStar_All.pipe_left
                                             (fun _0_39  -> Some _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4482 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4483 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4471
                                           uu____4482 e cret uu____4483 in
                                       (match uu____4468 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___143_4489 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___143_4489.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___143_4489.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4491 =
                                                let uu____4492 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4492 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4491
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4502 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4502
                                              then
                                                let uu____4503 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4503
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4509  ->
                             match uu___101_4509 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4511 -> [])) in
                   let lc1 =
                     let uu___144_4513 = lc in
                     let uu____4514 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4514;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___145_4516 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___145_4516.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___145_4516.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___145_4516.FStar_TypeChecker_Env.implicits)
                     } in
                   (e, lc1, g2))
let pure_or_ghost_pre_and_post:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ option* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t in
        let uu____4538 =
          let uu____4539 =
            let uu____4540 =
              let uu____4541 =
                let uu____4542 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4542 in
              [uu____4541] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4540 in
          uu____4539 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4538 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4551 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4551
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4562 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4571 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4588)::(ens,uu____4590)::uu____4591 ->
                    let uu____4613 =
                      let uu____4615 = norm req in Some uu____4615 in
                    let uu____4616 =
                      let uu____4617 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4617 in
                    (uu____4613, uu____4616)
                | uu____4619 ->
                    let uu____4625 =
                      let uu____4626 =
                        let uu____4629 =
                          let uu____4630 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4630 in
                        (uu____4629, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4626 in
                    raise uu____4625)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4640)::uu____4641 ->
                    let uu____4655 =
                      let uu____4658 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4658 in
                    (match uu____4655 with
                     | (us_r,uu____4675) ->
                         let uu____4676 =
                           let uu____4679 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4679 in
                         (match uu____4676 with
                          | (us_e,uu____4696) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4699 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4699
                                  us_r in
                              let as_ens =
                                let uu____4701 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4701
                                  us_e in
                              let req =
                                let uu____4705 =
                                  let uu____4706 =
                                    let uu____4707 =
                                      let uu____4714 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4714] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4707 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4706 in
                                uu____4705
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4730 =
                                  let uu____4731 =
                                    let uu____4732 =
                                      let uu____4739 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4739] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4732 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4731 in
                                uu____4730 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4752 =
                                let uu____4754 = norm req in Some uu____4754 in
                              let uu____4755 =
                                let uu____4756 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4756 in
                              (uu____4752, uu____4755)))
                | uu____4758 -> failwith "Impossible"))
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
      (let uu____4780 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4780
       then
         let uu____4781 = FStar_Syntax_Print.term_to_string tm in
         let uu____4782 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4781 uu____4782
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
            None head1.FStar_Syntax_Syntax.pos in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
        (let uu____4806 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4806
         then
           let uu____4807 = FStar_Syntax_Print.term_to_string tm in
           let uu____4808 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4807
             uu____4808
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4814 =
      let uu____4815 =
        let uu____4816 = FStar_Syntax_Subst.compress t in
        uu____4816.FStar_Syntax_Syntax.n in
      match uu____4815 with
      | FStar_Syntax_Syntax.Tm_app uu____4819 -> false
      | uu____4829 -> true in
    if uu____4814
    then t
    else
      (let uu____4831 = FStar_Syntax_Util.head_and_args t in
       match uu____4831 with
       | (head1,args) ->
           let uu____4857 =
             let uu____4858 =
               let uu____4859 = FStar_Syntax_Subst.compress head1 in
               uu____4859.FStar_Syntax_Syntax.n in
             match uu____4858 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4862 -> false in
           if uu____4857
           then
             (match args with
              | x::[] -> fst x
              | uu____4878 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
let maybe_instantiate:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____4909 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4909 with
             | (formals,uu____4918) ->
                 let n_implicits =
                   let uu____4930 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4967  ->
                             match uu____4967 with
                             | (uu____4971,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4930 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____5046 = FStar_TypeChecker_Env.expected_typ env in
             match uu____5046 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____5067 =
                     let uu____5068 =
                       let uu____5071 =
                         let uu____5072 = FStar_Util.string_of_int n_expected in
                         let uu____5079 = FStar_Syntax_Print.term_to_string e in
                         let uu____5080 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____5072 uu____5079 uu____5080 in
                       let uu____5087 = FStar_TypeChecker_Env.get_range env in
                       (uu____5071, uu____5087) in
                     FStar_Errors.Error uu____5068 in
                   raise uu____5067
                 else Some (n_available - n_expected) in
           let decr_inst uu___102_5105 =
             match uu___102_5105 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5124 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5124 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_40,uu____5185) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5207,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5226 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5226 with
                           | (v1,uu____5247,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5257 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5257 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5306 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5306)))
                      | (uu____5320,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5344 =
                      let uu____5358 = inst_n_binders t in
                      aux [] uu____5358 bs1 in
                    (match uu____5344 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5396) -> (e, torig, guard)
                          | (uu____5412,[]) when
                              let uu____5428 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5428 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5429 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5448 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5463 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5470 =
      let uu____5472 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5472
        (FStar_List.map
           (fun u  ->
              let uu____5477 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5477 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5470 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5491 = FStar_Util.set_is_empty x in
      if uu____5491
      then []
      else
        (let s =
           let uu____5496 =
             let uu____5498 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5498 in
           FStar_All.pipe_right uu____5496 FStar_Util.set_elements in
         (let uu____5503 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5503
          then
            let uu____5504 =
              let uu____5505 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5505 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5504
          else ());
         (let r =
            let uu____5510 = FStar_TypeChecker_Env.get_range env in
            Some uu____5510 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5518 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5518
                     then
                       let uu____5519 =
                         let uu____5520 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5520 in
                       let uu____5521 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5522 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5519 uu____5521 uu____5522
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
        let uu____5541 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5541 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_5571 =
  match uu___103_5571 with
  | None  -> ts
  | Some t ->
      let t1 = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange in
      let t2 = FStar_Syntax_Subst.close_univ_vars (fst ts) t1 in
      (FStar_ST.write (snd ts).FStar_Syntax_Syntax.tk
         (Some (t2.FStar_Syntax_Syntax.n));
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
        | ([],uu____5615) -> generalized_univ_names
        | (uu____5619,[]) -> explicit_univ_names
        | uu____5623 ->
            let uu____5628 =
              let uu____5629 =
                let uu____5632 =
                  let uu____5633 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5633 in
                (uu____5632, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5629 in
            raise uu____5628
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0 in
      let univnames1 = gather_free_univnames env t in
      let univs1 = FStar_Syntax_Free.univs t in
      (let uu____5649 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5649
       then
         let uu____5650 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5650
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5655 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5655
        then
          let uu____5656 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5656
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5661 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5661))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5693 =
        let uu____5694 =
          FStar_Util.for_all
            (fun uu____5699  ->
               match uu____5699 with
               | (uu____5704,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5694 in
      if uu____5693
      then None
      else
        (let norm c =
           (let uu____5727 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5727
            then
              let uu____5728 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5728
            else ());
           (let c1 =
              let uu____5731 = FStar_TypeChecker_Env.should_verify env in
              if uu____5731
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5734 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5734
             then
               let uu____5735 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5735
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5769 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5769 FStar_Util.set_elements in
         let uu____5813 =
           let uu____5831 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5886  ->
                     match uu____5886 with
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
           FStar_All.pipe_right uu____5831 FStar_List.unzip in
         match uu____5813 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____6043 = FStar_Syntax_Free.new_universe_uvar_set () in
               FStar_List.fold_left FStar_Util.set_union uu____6043 univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6050 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6050
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
                      (fun uu____6088  ->
                         match uu____6088 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6125  ->
                                       match uu____6125 with
                                       | (u,k) ->
                                           let uu____6133 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6133 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6139;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6140;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6141;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6147,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6149;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6150;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6151;_},uu____6152);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6153;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6154;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6155;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6173 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6177 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6180 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6180 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6204 =
                                                         let uu____6206 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              Some _0_41)
                                                           uu____6206 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6204 kres in
                                                     let t =
                                                       let uu____6209 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6209
                                                         (Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6212 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6230 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6230, c)
                               | ([],uu____6231) ->
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
                               | uu____6243 ->
                                   let uu____6251 = (e, c) in
                                   (match uu____6251 with
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
                                          let uu____6263 =
                                            let uu____6264 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6264.FStar_Syntax_Syntax.n in
                                          match uu____6263 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6281 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6281 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6291 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____6293 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6293)) in
                             (match uu____6212 with
                              | (e1,c1) -> (gen_univs1, e1, c1)))) in
               Some ecs1)))
let generalize:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.term*
      FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.univ_name Prims.list*
        FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____6333 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6333
       then
         let uu____6334 =
           let uu____6335 =
             FStar_List.map
               (fun uu____6340  ->
                  match uu____6340 with
                  | (lb,uu____6345,uu____6346) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6335 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6334
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6356  ->
              match uu____6356 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6371 =
           let uu____6378 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6394  ->
                     match uu____6394 with | (uu____6400,e,c) -> (e, c))) in
           gen env uu____6378 in
         match uu____6371 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6432  ->
                     match uu____6432 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6476  ->
                  fun uu____6477  ->
                    match (uu____6476, uu____6477) with
                    | ((l,uu____6510,uu____6511),(us,e,c)) ->
                        ((let uu____6537 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6537
                          then
                            let uu____6538 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6539 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6540 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6541 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6538 uu____6539 uu____6540 uu____6541
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6560  ->
              match uu____6560 with
              | (l,generalized_univs,t,c) ->
                  let uu____6578 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6578, t, c)) univnames_lecs generalized_lecs)
let check_and_ascribe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term* FStar_TypeChecker_Env.guard_t)
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
              (let uu____6615 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6615 with
               | None  -> None
               | Some f ->
                   let uu____6619 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_42  -> Some _0_42) uu____6619) in
          let is_var e1 =
            let uu____6625 =
              let uu____6626 = FStar_Syntax_Subst.compress e1 in
              uu____6626.FStar_Syntax_Syntax.n in
            match uu____6625 with
            | FStar_Syntax_Syntax.Tm_name uu____6629 -> true
            | uu____6630 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___146_6648 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___146_6648.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___146_6648.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6649 ->
                let uu___147_6650 = e2 in
                let uu____6651 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___147_6650.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6651;
                  FStar_Syntax_Syntax.pos =
                    (uu___147_6650.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___147_6650.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___148_6660 = env1 in
            let uu____6661 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_6660.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_6660.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_6660.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_6660.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_6660.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_6660.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_6660.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_6660.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_6660.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_6660.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_6660.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_6660.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_6660.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_6660.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_6660.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6661;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_6660.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_6660.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_6660.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_6660.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_6660.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_6660.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_6660.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_6660.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___148_6660.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___148_6660.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___148_6660.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6662 = check env2 t1 t2 in
          match uu____6662 with
          | None  ->
              let uu____6666 =
                let uu____6667 =
                  let uu____6670 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6671 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6670, uu____6671) in
                FStar_Errors.Error uu____6667 in
              raise uu____6666
          | Some g ->
              ((let uu____6676 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6676
                then
                  let uu____6677 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6677
                else ());
               (let uu____6679 = decorate e t2 in (uu____6679, g)))
let check_top_level:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool* FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
        let uu____6706 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6706
        then
          let uu____6709 = discharge g1 in
          let uu____6710 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6709, uu____6710)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6722 =
               let uu____6723 =
                 let uu____6724 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6724 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6723
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6722
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6726 = destruct_comp c1 in
           match uu____6726 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6738 = FStar_TypeChecker_Env.get_range env in
                 let uu____6739 =
                   let uu____6740 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6741 =
                     let uu____6742 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6743 =
                       let uu____6745 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6745] in
                     uu____6742 :: uu____6743 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6740 uu____6741 in
                 uu____6739
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6738 in
               ((let uu____6751 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6751
                 then
                   let uu____6752 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6752
                 else ());
                (let g2 =
                   let uu____6755 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6755 in
                 let uu____6756 = discharge g2 in
                 let uu____6757 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6756, uu____6757))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6783 =
        match uu___104_6783 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6789)::[] -> f fst1
        | uu____6802 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6807 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6807
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6816 =
          let uu____6819 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6819 in
        FStar_All.pipe_right uu____6816
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6830 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6830
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_6844 =
        match uu___105_6844 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6850)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6865)::[] ->
            let uu____6886 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6886
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6891 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6898 =
          let uu____6903 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6903) in
        let uu____6908 =
          let uu____6914 =
            let uu____6919 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6919) in
          let uu____6924 =
            let uu____6930 =
              let uu____6935 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6935) in
            let uu____6940 =
              let uu____6946 =
                let uu____6951 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6951) in
              let uu____6956 =
                let uu____6962 =
                  let uu____6967 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6967) in
                [uu____6962; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6946 :: uu____6956 in
            uu____6930 :: uu____6940 in
          uu____6914 :: uu____6924 in
        uu____6898 :: uu____6908 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7008 =
            FStar_Util.find_map table
              (fun uu____7014  ->
                 match uu____7014 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____7027 = mk1 seen_args in Some uu____7027
                     else None) in
          (match uu____7008 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____7030 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7035 =
      let uu____7036 = FStar_Syntax_Util.un_uinst l in
      uu____7036.FStar_Syntax_Syntax.n in
    match uu____7035 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____7040 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7060)::uu____7061 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7067 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7071,Some (FStar_Syntax_Syntax.Implicit uu____7072))::uu____7073
          -> bs
      | uu____7082 ->
          let uu____7083 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7083 with
           | None  -> bs
           | Some t ->
               let uu____7086 =
                 let uu____7087 = FStar_Syntax_Subst.compress t in
                 uu____7087.FStar_Syntax_Syntax.n in
               (match uu____7086 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7091) ->
                    let uu____7102 =
                      FStar_Util.prefix_until
                        (fun uu___106_7121  ->
                           match uu___106_7121 with
                           | (uu____7125,Some (FStar_Syntax_Syntax.Implicit
                              uu____7126)) -> false
                           | uu____7128 -> true) bs' in
                    (match uu____7102 with
                     | None  -> bs
                     | Some ([],uu____7146,uu____7147) -> bs
                     | Some (imps,uu____7184,uu____7185) ->
                         let uu____7222 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7230  ->
                                   match uu____7230 with
                                   | (x,uu____7235) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7222
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7258  ->
                                     match uu____7258 with
                                     | (x,i) ->
                                         let uu____7269 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7269, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7275 -> bs))
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
              (let uu____7299 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7299 e.FStar_Syntax_Syntax.pos)
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
          let uu____7325 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7325
          then e
          else
            (let uu____7327 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7327
               e.FStar_Syntax_Syntax.pos)
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____7357 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7357
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7359 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7359))
         else ());
        (let fv =
           let uu____7362 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7362 None in
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
         let uu____7369 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___149_7378 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_7378.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_7378.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_7378.FStar_Syntax_Syntax.sigmeta)
           }), uu____7369))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7390 =
        match uu___107_7390 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7391 -> false in
      let reducibility uu___108_7395 =
        match uu___108_7395 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7396 -> false in
      let assumption uu___109_7400 =
        match uu___109_7400 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7401 -> false in
      let reification uu___110_7405 =
        match uu___110_7405 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7406 -> true
        | uu____7407 -> false in
      let inferred uu___111_7411 =
        match uu___111_7411 with
        | FStar_Syntax_Syntax.Discriminator uu____7412 -> true
        | FStar_Syntax_Syntax.Projector uu____7413 -> true
        | FStar_Syntax_Syntax.RecordType uu____7416 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7421 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7426 -> false in
      let has_eq uu___112_7430 =
        match uu___112_7430 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7431 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7465 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7468 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7471 =
        let uu____7472 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7474  ->
                  match uu___113_7474 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7475 -> false)) in
        FStar_All.pipe_right uu____7472 Prims.op_Negation in
      if uu____7471
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7485 =
            let uu____7486 =
              let uu____7489 =
                let uu____7490 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7490 msg in
              (uu____7489, r) in
            FStar_Errors.Error uu____7486 in
          raise uu____7485 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7498 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7510 =
            let uu____7511 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7511 in
          if uu____7510 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7515),uu____7516,uu____7517) ->
              ((let uu____7528 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7528
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7531 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7531
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7535 ->
              let uu____7540 =
                let uu____7541 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7541 in
              if uu____7540 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7545 ->
              let uu____7549 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7549 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7552 ->
              let uu____7555 =
                let uu____7556 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7556 in
              if uu____7555 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7560 ->
              let uu____7561 =
                let uu____7562 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7562 in
              if uu____7561 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7566 ->
              let uu____7567 =
                let uu____7568 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7568 in
              if uu____7567 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7572 ->
              let uu____7579 =
                let uu____7580 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7580 in
              if uu____7579 then err'1 () else ()
          | uu____7584 -> ()))
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
                        FStar_Syntax_Syntax.gen_bv "projectee" (Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          let uu____7651 =
                            let uu____7654 =
                              let uu____7655 =
                                let uu____7660 =
                                  let uu____7661 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7661 in
                                (uu____7660, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7655 in
                            FStar_Syntax_Syntax.mk uu____7654 in
                          uu____7651 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7687  ->
                                  match uu____7687 with
                                  | (x,imp) ->
                                      let uu____7694 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7694, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7698 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7698 in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let x =
                             FStar_Syntax_Syntax.new_bv (Some p) arg_typ in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational None in
                             let uu____7707 =
                               let uu____7708 =
                                 let uu____7709 =
                                   let uu____7710 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7711 =
                                     let uu____7712 =
                                       let uu____7713 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7713 in
                                     [uu____7712] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7710
                                     uu____7711 in
                                 uu____7709 None p in
                               FStar_Syntax_Util.b2t uu____7708 in
                             FStar_Syntax_Util.refine x uu____7707 in
                           let uu____7718 =
                             let uu___150_7719 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_7719.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_7719.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7718) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7730 =
                          FStar_List.map
                            (fun uu____7740  ->
                               match uu____7740 with
                               | (x,uu____7747) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7730 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7771  ->
                                match uu____7771 with
                                | (x,uu____7778) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7787 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7787)
                               ||
                               (let uu____7788 =
                                  let uu____7789 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7789.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7788) in
                           let quals =
                             let uu____7792 =
                               let uu____7794 =
                                 let uu____7796 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7796
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7799 =
                                 FStar_List.filter
                                   (fun uu___114_7801  ->
                                      match uu___114_7801 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7802 -> false) iquals in
                               FStar_List.append uu____7794 uu____7799 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7792 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7815 =
                                 let uu____7816 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7816 in
                               FStar_Syntax_Syntax.mk_Total uu____7815 in
                             let uu____7817 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7817 in
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
                           (let uu____7820 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7820
                            then
                              let uu____7821 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7821
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Const.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____7849  ->
                                               match uu____7849 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7867 =
                                                       let uu____7870 =
                                                         let uu____7871 =
                                                           let uu____7876 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7876,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7871 in
                                                       pos uu____7870 in
                                                     (uu____7867, b)
                                                   else
                                                     (let uu____7880 =
                                                        let uu____7883 =
                                                          let uu____7884 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7884 in
                                                        pos uu____7883 in
                                                      (uu____7880, b)))) in
                                   let pat_true =
                                     let uu____7896 =
                                       let uu____7899 =
                                         let uu____7900 =
                                           let uu____7908 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7908, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7900 in
                                       pos uu____7899 in
                                     (uu____7896, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7930 =
                                       let uu____7933 =
                                         let uu____7934 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7934 in
                                       pos uu____7933 in
                                     (uu____7930, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7943 =
                                     let uu____7946 =
                                       let uu____7947 =
                                         let uu____7963 =
                                           let uu____7965 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7966 =
                                             let uu____7968 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7968] in
                                           uu____7965 :: uu____7966 in
                                         (arg_exp, uu____7963) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7947 in
                                     FStar_Syntax_Syntax.mk uu____7946 in
                                   uu____7943 None p) in
                              let dd =
                                let uu____7979 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7979
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational in
                              let imp =
                                FStar_Syntax_Util.abs binders body None in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun in
                              let lb =
                                let uu____7986 =
                                  let uu____7989 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7989 in
                                let uu____7990 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7986;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7990
                                } in
                              let impl =
                                let uu____7994 =
                                  let uu____7995 =
                                    let uu____8001 =
                                      let uu____8003 =
                                        let uu____8004 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8004
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8003] in
                                    ((false, [lb]), uu____8001, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7995 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7994;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____8019 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8019
                               then
                                 let uu____8020 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8020
                               else ());
                              [decl; impl])) in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name (fst arg_binder) in
                      let binders =
                        FStar_List.append imp_binders [arg_binder] in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8040  ->
                                  match uu____8040 with
                                  | (a,uu____8044) ->
                                      let uu____8045 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8045 with
                                       | (field_name,uu____8049) ->
                                           let field_proj_tm =
                                             let uu____8051 =
                                               let uu____8052 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8052 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8051 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8066 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8075  ->
                                    match uu____8075 with
                                    | (x,uu____8080) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8082 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8082 with
                                         | (field_name,uu____8087) ->
                                             let t =
                                               let uu____8089 =
                                                 let uu____8090 =
                                                   let uu____8093 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8093 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8090 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8089 in
                                             let only_decl =
                                               (let uu____8095 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Syntax_Const.prims_lid
                                                  uu____8095)
                                                 ||
                                                 (let uu____8096 =
                                                    let uu____8097 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8097.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8096) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8107 =
                                                   FStar_List.filter
                                                     (fun uu___115_8109  ->
                                                        match uu___115_8109
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8110 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8107
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_8118  ->
                                                         match uu___116_8118
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8119 ->
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
                                             ((let uu____8122 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8122
                                               then
                                                 let uu____8123 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8123
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     None
                                                     FStar_Syntax_Syntax.tun in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____8150  ->
                                                             match uu____8150
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8168
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8168,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8182
                                                                    =
                                                                    let uu____8185
                                                                    =
                                                                    let uu____8186
                                                                    =
                                                                    let uu____8191
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8191,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8186 in
                                                                    pos
                                                                    uu____8185 in
                                                                    (uu____8182,
                                                                    b))
                                                                   else
                                                                    (let uu____8195
                                                                    =
                                                                    let uu____8198
                                                                    =
                                                                    let uu____8199
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8199 in
                                                                    pos
                                                                    uu____8198 in
                                                                    (uu____8195,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8211 =
                                                     let uu____8214 =
                                                       let uu____8215 =
                                                         let uu____8223 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8223,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8215 in
                                                     pos uu____8214 in
                                                   let uu____8229 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8211, None,
                                                     uu____8229) in
                                                 let body =
                                                   let uu____8240 =
                                                     let uu____8243 =
                                                       let uu____8244 =
                                                         let uu____8260 =
                                                           let uu____8262 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8262] in
                                                         (arg_exp,
                                                           uu____8260) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8244 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8243 in
                                                   uu____8240 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8274 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8274
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
                                                   let uu____8280 =
                                                     let uu____8283 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8283 in
                                                   let uu____8284 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8280;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8284
                                                   } in
                                                 let impl =
                                                   let uu____8288 =
                                                     let uu____8289 =
                                                       let uu____8295 =
                                                         let uu____8297 =
                                                           let uu____8298 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8298
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8297] in
                                                       ((false, [lb]),
                                                         uu____8295, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8289 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8288;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8313 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8313
                                                  then
                                                    let uu____8314 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8314
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8066 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8348) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8351 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8351 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8364 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8364 with
                    | (formals,uu____8374) ->
                        let uu____8385 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8398 =
                                   let uu____8399 =
                                     let uu____8400 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8400 in
                                   FStar_Ident.lid_equals typ_lid uu____8399 in
                                 if uu____8398
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8410,uvs',tps,typ0,uu____8414,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8430 -> failwith "Impossible"
                                 else None) in
                          match tps_opt with
                          | Some x -> x
                          | None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Syntax_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____8385 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8472 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8472 with
                              | (indices,uu____8482) ->
                                  let refine_domain =
                                    let uu____8494 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_8496  ->
                                              match uu___117_8496 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8497 -> true
                                              | uu____8502 -> false)) in
                                    if uu____8494
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_8509 =
                                      match uu___118_8509 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8511,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8518 -> None in
                                    let uu____8519 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8519 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals in
                                  let fields =
                                    let uu____8527 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8527 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8558  ->
                                               fun uu____8559  ->
                                                 match (uu____8558,
                                                         uu____8559)
                                                 with
                                                 | ((x,uu____8569),(x',uu____8571))
                                                     ->
                                                     let uu____8576 =
                                                       let uu____8581 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8581) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8576) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8582 -> []