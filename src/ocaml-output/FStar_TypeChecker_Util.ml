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
  fun uu___98_73  ->
    match uu___98_73 with
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
                     let uu___118_190 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____191 =
                       let uu____199 =
                         let uu____206 = as_uvar u in
                         (reason, env, uu____206, t, k, r) in
                       [uu____199] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___118_190.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___118_190.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___118_190.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___119_386 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___119_386.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___119_386.FStar_Syntax_Syntax.index);
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
                       let uu____488 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____512  ->
                                 fun uu____513  ->
                                   match (uu____512, uu____513) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____555 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____555 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____488 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____616 = aux must_check_ty1 scope body in
                            (match uu____616 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____633 =
                                         FStar_Options.ml_ish () in
                                       if uu____633
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____640 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____640
                                   then
                                     let uu____641 =
                                       FStar_Range.string_of_range r in
                                     let uu____642 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____643 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____641 uu____642 uu____643
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____651 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____659 =
                            let uu____662 =
                              let uu____663 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____663
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____662 in
                          (uu____659, false)) in
                 let uu____670 =
                   let uu____675 = t_binders env in aux false uu____675 e in
                 match uu____670 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____692 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____692
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____696 =
                                let uu____697 =
                                  let uu____700 =
                                    let uu____701 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____701 in
                                  (uu____700, rng) in
                                FStar_Errors.Error uu____697 in
                              raise uu____696)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____708 ->
               let uu____709 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____709 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____793) ->
              let uu____798 = FStar_Syntax_Util.type_u () in
              (match uu____798 with
               | (k,uu____811) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___120_814 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___120_814.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___120_814.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____815 =
                     let uu____818 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____818 t in
                   (match uu____815 with
                    | (e,u) ->
                        let p2 =
                          let uu___121_833 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___121_833.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___121_833.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____840 = FStar_Syntax_Util.type_u () in
              (match uu____840 with
               | (t,uu____853) ->
                   let x1 =
                     let uu___122_855 = x in
                     let uu____856 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_855.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_855.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____856
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
              let uu____878 = FStar_Syntax_Util.type_u () in
              (match uu____878 with
               | (t,uu____891) ->
                   let x1 =
                     let uu___123_893 = x in
                     let uu____894 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_893.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_893.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____894
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
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
                             uu____1202 None p1.FStar_Syntax_Syntax.p in
                           (uu____1199,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1194 in
                       FStar_Syntax_Syntax.mk uu____1193 in
                     uu____1190 None p1.FStar_Syntax_Syntax.p in
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
                     (let uu___124_1246 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___124_1246.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___124_1246.FStar_Syntax_Syntax.p)
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
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1520 =
                                                   let uu____1522 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1522 in
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
                               | (uu____1591,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1592))
                                   when p_imp ->
                                   let uu____1594 = aux formals' pats' in
                                   (p2, true) :: uu____1594
                               | (uu____1606,Some
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
                                   let uu____1617 = aux formals' pats2 in
                                   (p3, true) :: uu____1617
                               | (uu____1629,imp) ->
                                   let uu____1633 =
                                     let uu____1638 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1638) in
                                   let uu____1641 = aux formals' pats' in
                                   uu____1633 :: uu____1641) in
                        let uu___125_1651 = p1 in
                        let uu____1654 =
                          let uu____1655 =
                            let uu____1663 = aux f pats1 in (fv, uu____1663) in
                          FStar_Syntax_Syntax.Pat_cons uu____1655 in
                        {
                          FStar_Syntax_Syntax.v = uu____1654;
                          FStar_Syntax_Syntax.ty =
                            (uu___125_1651.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___125_1651.FStar_Syntax_Syntax.p)
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
               | Some x ->
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
          | (uu____1820,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1822)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1827,FStar_Syntax_Syntax.Tm_constant uu____1828) ->
              let uu____1829 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1829
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1833 =
                    let uu____1834 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1835 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1834 uu____1835 in
                  failwith uu____1833)
               else ();
               (let uu____1838 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1838
                then
                  let uu____1839 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1840 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1839
                    uu____1840
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1844 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1844.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1844.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1848 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1848
                then
                  let uu____1849 =
                    let uu____1850 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1851 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1850 uu____1851 in
                  failwith uu____1849
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_1855 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_1855.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_1855.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1857),uu____1858) ->
              let s = force_sort e1 in
              let x1 =
                let uu___128_1867 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___128_1867.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___128_1867.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1880 =
                  let uu____1881 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1881 in
                if uu____1880
                then
                  let uu____1882 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1882
                else ());
               (let uu____1892 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1892))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1905;
                FStar_Syntax_Syntax.pos = uu____1906;
                FStar_Syntax_Syntax.vars = uu____1907;_},args))
              ->
              ((let uu____1934 =
                  let uu____1935 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1935 Prims.op_Negation in
                if uu____1934
                then
                  let uu____1936 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1936
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2024 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2024
                  | (arg::args2,(argpat,uu____2037)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2087) ->
                           let x =
                             let uu____2103 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2103 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2117) ->
                           let pat =
                             let uu____2132 = aux argpat e2 in
                             let uu____2133 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2132, uu____2133) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2136 ->
                      let uu____2150 =
                        let uu____2151 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2152 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2151 uu____2152 in
                      failwith uu____2150 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2162;
                     FStar_Syntax_Syntax.pos = uu____2163;
                     FStar_Syntax_Syntax.vars = uu____2164;_},uu____2165);
                FStar_Syntax_Syntax.tk = uu____2166;
                FStar_Syntax_Syntax.pos = uu____2167;
                FStar_Syntax_Syntax.vars = uu____2168;_},args))
              ->
              ((let uu____2199 =
                  let uu____2200 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2200 Prims.op_Negation in
                if uu____2199
                then
                  let uu____2201 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2201
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2289 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2289
                  | (arg::args2,(argpat,uu____2302)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2352) ->
                           let x =
                             let uu____2368 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2368 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2382) ->
                           let pat =
                             let uu____2397 = aux argpat e2 in
                             let uu____2398 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2397, uu____2398) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2401 ->
                      let uu____2415 =
                        let uu____2416 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2417 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2416 uu____2417 in
                      failwith uu____2415 in
                match_args [] args argpats))
          | uu____2424 ->
              let uu____2427 =
                let uu____2428 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2429 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2430 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2428 uu____2429 uu____2430 in
              failwith uu____2427 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2465 =
      match uu____2465 with
      | (p,i) ->
          let uu____2475 = decorated_pattern_as_term p in
          (match uu____2475 with
           | (vars,te) ->
               let uu____2488 =
                 let uu____2491 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2491) in
               (vars, uu____2488)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2499 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2499)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2502 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2502)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2505 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2505)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2519 =
          let uu____2527 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2527 FStar_List.unzip in
        (match uu____2519 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2585 =
               let uu____2586 =
                 let uu____2587 =
                   let uu____2597 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2597, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2587 in
               mk1 uu____2586 in
             (vars1, uu____2585))
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
      | (wp,uu____2627)::[] -> wp
      | uu____2640 ->
          let uu____2646 =
            let uu____2647 =
              let uu____2648 =
                FStar_List.map
                  (fun uu____2652  ->
                     match uu____2652 with
                     | (x,uu____2656) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2648 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2647 in
          failwith uu____2646 in
    let uu____2660 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2660, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2677 = destruct_comp c in
        match uu____2677 with
        | (u,uu____2682,wp) ->
            let uu____2684 =
              let uu____2690 =
                let uu____2691 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2691 in
              [uu____2690] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2684;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2704 =
          let uu____2708 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2709 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2708 uu____2709 in
        match uu____2704 with | (m,uu____2711,uu____2712) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2725 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2725
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
        let uu____2753 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2753 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2775 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2775 with
             | (a,kwp) ->
                 let uu____2792 = destruct_comp m1 in
                 let uu____2796 = destruct_comp m2 in
                 ((md, a, kwp), uu____2792, uu____2796))
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
            let uu____2853 =
              let uu____2854 =
                let uu____2860 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2860] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2854;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2853
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
      let uu___129_2907 = lc in
      let uu____2908 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___129_2907.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2908;
        FStar_Syntax_Syntax.cflags =
          (uu___129_2907.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2911  ->
             let uu____2912 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2912)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2917 =
      let uu____2918 = FStar_Syntax_Subst.compress t in
      uu____2918.FStar_Syntax_Syntax.n in
    match uu____2917 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2921 -> true
    | uu____2929 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2944 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2944
        then c
        else
          (let uu____2946 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2946
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2976 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2976] in
                       let us =
                         let uu____2979 =
                           let uu____2981 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2981] in
                         u_res :: uu____2979 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2992 =
                         let uu____2993 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2994 =
                           let uu____2995 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2996 =
                             let uu____2998 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2999 =
                               let uu____3001 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____3001] in
                             uu____2998 :: uu____2999 in
                           uu____2995 :: uu____2996 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2993 uu____2994 in
                       uu____2992 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____3007 = destruct_comp c1 in
              match uu____3007 with
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
        let close1 uu____3033 =
          let uu____3034 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____3034 in
        let uu___130_3035 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___130_3035.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___130_3035.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___130_3035.FStar_Syntax_Syntax.cflags);
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
          let uu____3049 =
            let uu____3050 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____3050 in
          if uu____3049
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____3055 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____3055
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____3057 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____3057 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____3063 =
                        let uu____3064 =
                          let uu____3065 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3066 =
                            let uu____3067 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3068 =
                              let uu____3070 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3070] in
                            uu____3067 :: uu____3068 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3065 uu____3066 in
                        uu____3064 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____3063) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3076 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3076
         then
           let uu____3077 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3078 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3079 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3077
             uu____3078 uu____3079
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
          fun uu____3101  ->
            match uu____3101 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3111 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3111
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3114 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3116 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3117 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3114 uu____3116 bstr uu____3117
                  else ());
                 (let bind_it uu____3122 =
                    let uu____3123 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3123
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3133 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3133
                        then
                          let uu____3134 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3136 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3137 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3138 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3139 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3134 uu____3136 uu____3137 uu____3138
                            uu____3139
                        else ());
                       (let try_simplify uu____3150 =
                          let aux uu____3160 =
                            let uu____3161 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3161
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3180 ->
                                  let uu____3181 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3181
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3200 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3200
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3236 =
                                  let uu____3239 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3239, reason) in
                                FStar_Util.Inl uu____3236
                            | uu____3242 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3257 =
                              let uu____3258 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3258.FStar_Syntax_Syntax.n in
                            match uu____3257 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3262) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3268 -> c in
                          let uu____3269 =
                            let uu____3270 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3270 in
                          if uu____3269
                          then
                            let uu____3278 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3278
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3292 =
                                  let uu____3293 =
                                    let uu____3296 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3296) in
                                  FStar_Errors.Error uu____3293 in
                                raise uu____3292))
                          else
                            (let uu____3304 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3304
                             then subst_c2 "both total"
                             else
                               (let uu____3312 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3312
                                then
                                  let uu____3319 =
                                    let uu____3322 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3322, "both gtot") in
                                  FStar_Util.Inl uu____3319
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3338 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3339 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3339) in
                                       if uu____3338
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___131_3348 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___131_3348.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___131_3348.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3349 =
                                           let uu____3352 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3352, "c1 Tot") in
                                         FStar_Util.Inl uu____3349
                                       else aux ()
                                   | uu____3356 -> aux ()))) in
                        let uu____3361 = try_simplify () in
                        match uu____3361 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3379 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3379
                              then
                                let uu____3380 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3381 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3382 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3380 uu____3381 uu____3382
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3389 = lift_and_destruct env c1 c2 in
                            (match uu____3389 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3423 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3423]
                                   | Some x ->
                                       let uu____3425 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3425] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (Some
                                        (FStar_Util.Inr
                                           (FStar_Syntax_Const.effect_Tot_lid,
                                             [FStar_Syntax_Syntax.TOTAL]))) in
                                 let r11 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_range r1)) None r1 in
                                 let wp_args =
                                   let uu____3448 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3449 =
                                     let uu____3451 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3452 =
                                       let uu____3454 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3455 =
                                         let uu____3457 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3458 =
                                           let uu____3460 =
                                             let uu____3461 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3461 in
                                           [uu____3460] in
                                         uu____3457 :: uu____3458 in
                                       uu____3454 :: uu____3455 in
                                     uu____3451 :: uu____3452 in
                                   uu____3448 :: uu____3449 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3466 =
                                     let uu____3467 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3467
                                       wp_args in
                                   uu____3466 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3518 =
                let uu____3519 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3519 in
              if uu____3518
              then f
              else (let uu____3521 = reason1 () in label uu____3521 r f)
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
            let uu___132_3535 = g in
            let uu____3536 =
              let uu____3537 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3537 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3536;
              FStar_TypeChecker_Env.deferred =
                (uu___132_3535.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_3535.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_3535.FStar_TypeChecker_Env.implicits)
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
      | uu____3549 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3569 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3573 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3573
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3580 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3580
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3585 = destruct_comp c1 in
                    match uu____3585 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3598 =
                            let uu____3599 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3600 =
                              let uu____3601 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3602 =
                                let uu____3604 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3605 =
                                  let uu____3607 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3607] in
                                uu____3604 :: uu____3605 in
                              uu____3601 :: uu____3602 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3599
                              uu____3600 in
                          uu____3598 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___133_3612 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___133_3612.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___133_3612.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___133_3612.FStar_Syntax_Syntax.cflags);
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
            let uu____3644 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3644
            then (lc, g0)
            else
              ((let uu____3649 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3649
                then
                  let uu____3650 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3651 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3650 uu____3651
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___99_3657  ->
                          match uu___99_3657 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3659 -> [])) in
                let strengthen uu____3665 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3673 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3673 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3680 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3681 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3681) in
                           if uu____3680
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3688 =
                                 let uu____3689 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3689 in
                               FStar_Syntax_Util.comp_set_flags uu____3688
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3694 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3694
                           then
                             let uu____3695 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3696 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3695 uu____3696
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3699 = destruct_comp c2 in
                           match uu____3699 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3712 =
                                   let uu____3713 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3714 =
                                     let uu____3715 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3716 =
                                       let uu____3718 =
                                         let uu____3719 =
                                           let uu____3720 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3720 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3719 in
                                       let uu____3721 =
                                         let uu____3723 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3723] in
                                       uu____3718 :: uu____3721 in
                                     uu____3715 :: uu____3716 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3713
                                     uu____3714 in
                                 uu____3712 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3729 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3729
                                 then
                                   let uu____3730 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3730
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3733 =
                  let uu___134_3734 = lc in
                  let uu____3735 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3736 =
                    let uu____3738 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3739 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3739) in
                    if uu____3738 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3735;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___134_3734.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3736;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3733,
                  (let uu___135_3742 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___135_3742.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___135_3742.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___135_3742.FStar_TypeChecker_Env.implicits)
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
        let uu____3760 =
          let uu____3763 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3764 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3763, uu____3764) in
        match uu____3760 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3773 =
                let uu____3774 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3775 =
                  let uu____3776 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3777 =
                    let uu____3779 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3779] in
                  uu____3776 :: uu____3777 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3774 uu____3775 in
              uu____3773 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3787 =
                let uu____3788 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3789 =
                  let uu____3790 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3791 =
                    let uu____3793 =
                      let uu____3794 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3794 in
                    let uu____3795 =
                      let uu____3797 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3797] in
                    uu____3793 :: uu____3795 in
                  uu____3790 :: uu____3791 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3788 uu____3789 in
              uu____3787 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3805 =
                let uu____3806 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3807 =
                  let uu____3808 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3809 =
                    let uu____3811 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3812 =
                      let uu____3814 =
                        let uu____3815 =
                          let uu____3816 =
                            let uu____3817 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3817] in
                          FStar_Syntax_Util.abs uu____3816 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3815 in
                      [uu____3814] in
                    uu____3811 :: uu____3812 in
                  uu____3808 :: uu____3809 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3806 uu____3807 in
              uu____3805 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3833 = FStar_TypeChecker_Env.get_range env in
              bind uu____3833 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3855 =
            let uu____3856 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3856
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3859 =
                 let uu____3872 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3873 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3872 uu____3873 in
               match uu____3859 with
               | ((md,uu____3875,uu____3876),(u_res_t,res_t,wp_then),
                  (uu____3880,uu____3881,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3910 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3911 =
                       let uu____3912 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3913 =
                         let uu____3914 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3915 =
                           let uu____3917 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3918 =
                             let uu____3920 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3921 =
                               let uu____3923 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3923] in
                             uu____3920 :: uu____3921 in
                           uu____3917 :: uu____3918 in
                         uu____3914 :: uu____3915 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3912 uu____3913 in
                     uu____3911 None uu____3910 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3931 =
                     let uu____3932 = FStar_Options.split_cases () in
                     uu____3932 > (Prims.parse_int "0") in
                   if uu____3931
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3938 =
                          let uu____3939 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3940 =
                            let uu____3941 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3942 =
                              let uu____3944 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3944] in
                            uu____3941 :: uu____3942 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3939 uu____3940 in
                        uu____3938 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3949 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3949;
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
      let uu____3958 =
        let uu____3959 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3959 in
      FStar_Syntax_Syntax.fvar uu____3958 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3982  ->
                 match uu____3982 with
                 | (uu____3985,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3990 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3992 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3992
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____4012 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____4013 =
                 let uu____4014 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____4015 =
                   let uu____4016 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____4017 =
                     let uu____4019 = FStar_Syntax_Syntax.as_arg g in
                     let uu____4020 =
                       let uu____4022 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____4023 =
                         let uu____4025 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____4025] in
                       uu____4022 :: uu____4023 in
                     uu____4019 :: uu____4020 in
                   uu____4016 :: uu____4017 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4014 uu____4015 in
               uu____4013 None uu____4012 in
             let default_case =
               let post_k =
                 let uu____4034 =
                   let uu____4038 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____4038] in
                 let uu____4039 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4034 uu____4039 in
               let kwp =
                 let uu____4045 =
                   let uu____4049 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____4049] in
                 let uu____4050 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4045 uu____4050 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____4055 =
                   let uu____4056 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____4056] in
                 let uu____4057 =
                   let uu____4058 =
                     let uu____4061 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____4061 in
                   let uu____4062 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____4058 uu____4062 in
                 FStar_Syntax_Util.abs uu____4055 uu____4057
                   (Some
                      (FStar_Util.Inr
                         (FStar_Syntax_Const.effect_Tot_lid,
                           [FStar_Syntax_Syntax.TOTAL]))) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Syntax_Const.effect_PURE_lid in
               mk_comp md u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____4076  ->
                    fun celse  ->
                      match uu____4076 with
                      | (g,cthen) ->
                          let uu____4082 =
                            let uu____4095 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____4095 celse in
                          (match uu____4082 with
                           | ((md,uu____4097,uu____4098),(uu____4099,uu____4100,wp_then),
                              (uu____4102,uu____4103,wp_else)) ->
                               let uu____4114 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4114 []))
                 lcases default_case in
             let uu____4115 =
               let uu____4116 = FStar_Options.split_cases () in
               uu____4116 > (Prims.parse_int "0") in
             if uu____4115
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4120 = destruct_comp comp1 in
                match uu____4120 with
                | (uu____4124,uu____4125,wp) ->
                    let wp1 =
                      let uu____4130 =
                        let uu____4131 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4132 =
                          let uu____4133 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4134 =
                            let uu____4136 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4136] in
                          uu____4133 :: uu____4134 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4131 uu____4132 in
                      uu____4130 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4155 =
            ((let uu____4156 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4156) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4157 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4157) in
          if uu____4155
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4165 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4169 =
            (let uu____4170 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4170) || env.FStar_TypeChecker_Env.lax in
          if uu____4169
          then c
          else
            (let uu____4174 = FStar_Syntax_Util.is_partial_return c in
             if uu____4174
             then c
             else
               (let uu____4178 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4178
                then
                  let uu____4181 =
                    let uu____4182 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4182 in
                  (if uu____4181
                   then
                     let uu____4185 =
                       let uu____4186 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4187 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4186 uu____4187 in
                     failwith uu____4185
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4192 =
                        let uu____4193 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4193 in
                      if uu____4192
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___136_4198 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___136_4198.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___136_4198.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___136_4198.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4209 =
                       let uu____4212 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4212
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4209 in
                   let eq1 =
                     let uu____4216 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4216 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4218 =
                     let uu____4219 =
                       let uu____4224 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4224.FStar_Syntax_Syntax.comp in
                     uu____4219 () in
                   FStar_Syntax_Util.comp_set_flags uu____4218 flags))) in
        let uu___137_4226 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4226.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4226.FStar_Syntax_Syntax.res_typ);
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
          let uu____4249 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4249 with
          | None  ->
              let uu____4254 =
                let uu____4255 =
                  let uu____4258 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4259 = FStar_TypeChecker_Env.get_range env in
                  (uu____4258, uu____4259) in
                FStar_Errors.Error uu____4255 in
              raise uu____4254
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
            let uu____4289 =
              let uu____4290 = FStar_Syntax_Subst.compress t2 in
              uu____4290.FStar_Syntax_Syntax.n in
            match uu____4289 with
            | FStar_Syntax_Syntax.Tm_type uu____4293 -> true
            | uu____4294 -> false in
          let uu____4295 =
            let uu____4296 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4296.FStar_Syntax_Syntax.n in
          match uu____4295 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4302 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4309 =
                  let uu____4310 =
                    let uu____4311 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4311 in
                  (None, uu____4310) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4309 in
              let e1 =
                let uu____4320 =
                  let uu____4321 =
                    let uu____4322 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4322] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4321 in
                uu____4320
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4329 -> (e, lc)
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
              (let uu____4353 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4353 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4366 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4378 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4378, false)
            else
              (let uu____4382 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4382, true)) in
          match gopt with
          | (None ,uu____4388) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___138_4391 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___138_4391.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___138_4391.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___138_4391.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4395 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4395 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___139_4400 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_4400.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_4400.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___139_4400.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___140_4403 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___140_4403.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___140_4403.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___140_4403.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4409 =
                     let uu____4410 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4410
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4415 =
                          let uu____4416 = FStar_Syntax_Subst.compress f1 in
                          uu____4416.FStar_Syntax_Syntax.n in
                        match uu____4415 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4421,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4423;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4424;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4425;_},uu____4426)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___141_4450 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___141_4450.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___141_4450.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___141_4450.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4451 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4456 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4456
                              then
                                let uu____4457 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4458 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4459 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4460 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4457 uu____4458 uu____4459 uu____4460
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4463 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4463 with
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
                                  let uu____4474 = destruct_comp ct in
                                  (match uu____4474 with
                                   | (u_t,uu____4481,uu____4482) ->
                                       let wp =
                                         let uu____4486 =
                                           let uu____4487 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4488 =
                                             let uu____4489 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4490 =
                                               let uu____4492 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4492] in
                                             uu____4489 :: uu____4490 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4487 uu____4488 in
                                         uu____4486
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4498 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4498 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4508 =
                                             let uu____4509 =
                                               let uu____4510 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4510] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4509 in
                                           uu____4508
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4516 =
                                         let uu____4519 =
                                           FStar_All.pipe_left
                                             (fun _0_39  -> Some _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4530 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4531 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4519
                                           uu____4530 e cret uu____4531 in
                                       (match uu____4516 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___142_4537 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___142_4537.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___142_4537.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4539 =
                                                let uu____4540 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4540 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4539
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4550 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4550
                                              then
                                                let uu____4551 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4551
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___100_4557  ->
                             match uu___100_4557 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4559 -> [])) in
                   let lc1 =
                     let uu___143_4561 = lc in
                     let uu____4562 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4562;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___144_4564 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_4564.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_4564.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_4564.FStar_TypeChecker_Env.implicits)
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
        let uu____4586 =
          let uu____4587 =
            let uu____4588 =
              let uu____4589 =
                let uu____4590 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4590 in
              [uu____4589] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4588 in
          uu____4587 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4586 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4599 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4599
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4610 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4619 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4636)::(ens,uu____4638)::uu____4639 ->
                    let uu____4661 =
                      let uu____4663 = norm req in Some uu____4663 in
                    let uu____4664 =
                      let uu____4665 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4665 in
                    (uu____4661, uu____4664)
                | uu____4667 ->
                    let uu____4673 =
                      let uu____4674 =
                        let uu____4677 =
                          let uu____4678 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4678 in
                        (uu____4677, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4674 in
                    raise uu____4673)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4688)::uu____4689 ->
                    let uu____4703 =
                      let uu____4706 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4706 in
                    (match uu____4703 with
                     | (us_r,uu____4723) ->
                         let uu____4724 =
                           let uu____4727 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4727 in
                         (match uu____4724 with
                          | (us_e,uu____4744) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4747 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4747
                                  us_r in
                              let as_ens =
                                let uu____4749 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4749
                                  us_e in
                              let req =
                                let uu____4753 =
                                  let uu____4754 =
                                    let uu____4755 =
                                      let uu____4762 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4762] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4755 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4754 in
                                uu____4753
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4778 =
                                  let uu____4779 =
                                    let uu____4780 =
                                      let uu____4787 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4787] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4780 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4779 in
                                uu____4778 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4800 =
                                let uu____4802 = norm req in Some uu____4802 in
                              let uu____4803 =
                                let uu____4804 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4804 in
                              (uu____4800, uu____4803)))
                | uu____4806 -> failwith "Impossible"))
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
      (let uu____4828 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4828
       then
         let uu____4829 = FStar_Syntax_Print.term_to_string tm in
         let uu____4830 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4829 uu____4830
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
        (let uu____4854 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4854
         then
           let uu____4855 = FStar_Syntax_Print.term_to_string tm in
           let uu____4856 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4855
             uu____4856
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4862 =
      let uu____4863 =
        let uu____4864 = FStar_Syntax_Subst.compress t in
        uu____4864.FStar_Syntax_Syntax.n in
      match uu____4863 with
      | FStar_Syntax_Syntax.Tm_app uu____4867 -> false
      | uu____4877 -> true in
    if uu____4862
    then t
    else
      (let uu____4879 = FStar_Syntax_Util.head_and_args t in
       match uu____4879 with
       | (head1,args) ->
           let uu____4905 =
             let uu____4906 =
               let uu____4907 = FStar_Syntax_Subst.compress head1 in
               uu____4907.FStar_Syntax_Syntax.n in
             match uu____4906 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4910 -> false in
           if uu____4905
           then
             (match args with
              | x::[] -> fst x
              | uu____4926 ->
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
             let uu____4957 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4957 with
             | (formals,uu____4966) ->
                 let n_implicits =
                   let uu____4978 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____5015  ->
                             match uu____5015 with
                             | (uu____5019,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4978 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____5094 = FStar_TypeChecker_Env.expected_typ env in
             match uu____5094 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____5115 =
                     let uu____5116 =
                       let uu____5119 =
                         let uu____5120 = FStar_Util.string_of_int n_expected in
                         let uu____5127 = FStar_Syntax_Print.term_to_string e in
                         let uu____5128 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____5120 uu____5127 uu____5128 in
                       let uu____5135 = FStar_TypeChecker_Env.get_range env in
                       (uu____5119, uu____5135) in
                     FStar_Errors.Error uu____5116 in
                   raise uu____5115
                 else Some (n_available - n_expected) in
           let decr_inst uu___101_5153 =
             match uu___101_5153 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5172 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5172 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_40,uu____5233) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5255,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5274 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5274 with
                           | (v1,uu____5295,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5305 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5305 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5354 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5354)))
                      | (uu____5368,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5392 =
                      let uu____5406 = inst_n_binders t in
                      aux [] uu____5406 bs1 in
                    (match uu____5392 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5444) -> (e, torig, guard)
                          | (uu____5460,[]) when
                              let uu____5476 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5476 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5477 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5496 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5511 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5518 =
      let uu____5520 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5520
        (FStar_List.map
           (fun u  ->
              let uu____5525 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5525 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5518 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5539 = FStar_Util.set_is_empty x in
      if uu____5539
      then []
      else
        (let s =
           let uu____5544 =
             let uu____5546 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5546 in
           FStar_All.pipe_right uu____5544 FStar_Util.set_elements in
         (let uu____5551 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5551
          then
            let uu____5552 =
              let uu____5553 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5553 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5552
          else ());
         (let r =
            let uu____5558 = FStar_TypeChecker_Env.get_range env in
            Some uu____5558 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5566 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5566
                     then
                       let uu____5567 =
                         let uu____5568 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5568 in
                       let uu____5569 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5570 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5567 uu____5569 uu____5570
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
        let uu____5589 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5589 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___102_5619 =
  match uu___102_5619 with
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
        | ([],uu____5663) -> generalized_univ_names
        | (uu____5667,[]) -> explicit_univ_names
        | uu____5671 ->
            let uu____5676 =
              let uu____5677 =
                let uu____5680 =
                  let uu____5681 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5681 in
                (uu____5680, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5677 in
            raise uu____5676
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
      (let uu____5697 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5697
       then
         let uu____5698 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5698
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5703 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5703
        then
          let uu____5704 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5704
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5709 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5709))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5741 =
        let uu____5742 =
          FStar_Util.for_all
            (fun uu____5747  ->
               match uu____5747 with
               | (uu____5752,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5742 in
      if uu____5741
      then None
      else
        (let norm c =
           (let uu____5775 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5775
            then
              let uu____5776 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5776
            else ());
           (let c1 =
              let uu____5779 = FStar_TypeChecker_Env.should_verify env in
              if uu____5779
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5782 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5782
             then
               let uu____5783 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5783
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5817 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5817 FStar_Util.set_elements in
         let uu____5861 =
           let uu____5879 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5934  ->
                     match uu____5934 with
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
           FStar_All.pipe_right uu____5879 FStar_List.unzip in
         match uu____5861 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____6091 = FStar_Syntax_Free.new_universe_uvar_set () in
               FStar_List.fold_left FStar_Util.set_union uu____6091 univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6098 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6098
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
                      (fun uu____6136  ->
                         match uu____6136 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6173  ->
                                       match uu____6173 with
                                       | (u,k) ->
                                           let uu____6181 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6181 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6187;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6188;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6189;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6195,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6197;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6198;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6199;_},uu____6200);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6201;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6202;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6203;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6231 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6235 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6238 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6238 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6262 =
                                                         let uu____6264 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              Some _0_41)
                                                           uu____6264 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6262 kres in
                                                     let t =
                                                       let uu____6267 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6268 =
                                                         let uu____6275 =
                                                           let uu____6281 =
                                                             let uu____6282 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6282 in
                                                           FStar_Util.Inl
                                                             uu____6281 in
                                                         Some uu____6275 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6267
                                                         uu____6268 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6295 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6313 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6313, c)
                               | ([],uu____6314) ->
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
                               | uu____6326 ->
                                   let uu____6334 = (e, c) in
                                   (match uu____6334 with
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
                                          let uu____6346 =
                                            let uu____6347 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6347.FStar_Syntax_Syntax.n in
                                          match uu____6346 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6364 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6364 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6374 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6384 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6384)) in
                             (match uu____6295 with
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
      (let uu____6424 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6424
       then
         let uu____6425 =
           let uu____6426 =
             FStar_List.map
               (fun uu____6431  ->
                  match uu____6431 with
                  | (lb,uu____6436,uu____6437) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6426 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6425
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6447  ->
              match uu____6447 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6462 =
           let uu____6469 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6485  ->
                     match uu____6485 with | (uu____6491,e,c) -> (e, c))) in
           gen env uu____6469 in
         match uu____6462 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6523  ->
                     match uu____6523 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6567  ->
                  fun uu____6568  ->
                    match (uu____6567, uu____6568) with
                    | ((l,uu____6601,uu____6602),(us,e,c)) ->
                        ((let uu____6628 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6628
                          then
                            let uu____6629 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6630 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6631 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6632 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6629 uu____6630 uu____6631 uu____6632
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6651  ->
              match uu____6651 with
              | (l,generalized_univs,t,c) ->
                  let uu____6669 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6669, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6706 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6706 with
               | None  -> None
               | Some f ->
                   let uu____6710 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_42  -> Some _0_42) uu____6710) in
          let is_var e1 =
            let uu____6716 =
              let uu____6717 = FStar_Syntax_Subst.compress e1 in
              uu____6717.FStar_Syntax_Syntax.n in
            match uu____6716 with
            | FStar_Syntax_Syntax.Tm_name uu____6720 -> true
            | uu____6721 -> false in
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
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6740 ->
                let uu___146_6741 = e2 in
                let uu____6742 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
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
                (uu___147_6751.FStar_TypeChecker_Env.synth)
            } in
          let uu____6753 = check env2 t1 t2 in
          match uu____6753 with
          | None  ->
              let uu____6757 =
                let uu____6758 =
                  let uu____6761 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6762 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6761, uu____6762) in
                FStar_Errors.Error uu____6758 in
              raise uu____6757
          | Some g ->
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
      FStar_Syntax_Syntax.lcomp -> (Prims.bool* FStar_Syntax_Syntax.comp)
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
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
      let short_bin_op f uu___103_6874 =
        match uu___103_6874 with
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
      let short_op_ite uu___104_6935 =
        match uu___104_6935 with
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
          (FStar_Syntax_Const.op_And, uu____6994) in
        let uu____6999 =
          let uu____7005 =
            let uu____7010 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____7010) in
          let uu____7015 =
            let uu____7021 =
              let uu____7026 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____7026) in
            let uu____7031 =
              let uu____7037 =
                let uu____7042 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____7042) in
              let uu____7047 =
                let uu____7053 =
                  let uu____7058 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____7058) in
                [uu____7053; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____7037 :: uu____7047 in
            uu____7021 :: uu____7031 in
          uu____7005 :: uu____7015 in
        uu____6989 :: uu____6999 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7099 =
            FStar_Util.find_map table
              (fun uu____7105  ->
                 match uu____7105 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____7118 = mk1 seen_args in Some uu____7118
                     else None) in
          (match uu____7099 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____7121 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7126 =
      let uu____7127 = FStar_Syntax_Util.un_uinst l in
      uu____7127.FStar_Syntax_Syntax.n in
    match uu____7126 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
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
      | (uu____7162,Some (FStar_Syntax_Syntax.Implicit uu____7163))::uu____7164
          -> bs
      | uu____7173 ->
          let uu____7174 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7174 with
           | None  -> bs
           | Some t ->
               let uu____7177 =
                 let uu____7178 = FStar_Syntax_Subst.compress t in
                 uu____7178.FStar_Syntax_Syntax.n in
               (match uu____7177 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7182) ->
                    let uu____7193 =
                      FStar_Util.prefix_until
                        (fun uu___105_7212  ->
                           match uu___105_7212 with
                           | (uu____7216,Some (FStar_Syntax_Syntax.Implicit
                              uu____7217)) -> false
                           | uu____7219 -> true) bs' in
                    (match uu____7193 with
                     | None  -> bs
                     | Some ([],uu____7237,uu____7238) -> bs
                     | Some (imps,uu____7275,uu____7276) ->
                         let uu____7313 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7321  ->
                                   match uu____7321 with
                                   | (x,uu____7326) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7313
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7349  ->
                                     match uu____7349 with
                                     | (x,i) ->
                                         let uu____7360 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7360, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7366 -> bs))
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
              (let uu____7390 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7390 e.FStar_Syntax_Syntax.pos)
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
          let uu____7416 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7416
          then e
          else
            (let uu____7418 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7418
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
        (let uu____7448 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7448
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7450 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7450))
         else ());
        (let fv =
           let uu____7453 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7453 None in
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
         let uu____7460 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___148_7469 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___148_7469.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___148_7469.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___148_7469.FStar_Syntax_Syntax.sigmeta)
           }), uu____7460))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___106_7481 =
        match uu___106_7481 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7482 -> false in
      let reducibility uu___107_7486 =
        match uu___107_7486 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7487 -> false in
      let assumption uu___108_7491 =
        match uu___108_7491 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7492 -> false in
      let reification uu___109_7496 =
        match uu___109_7496 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7497 -> true
        | uu____7498 -> false in
      let inferred uu___110_7502 =
        match uu___110_7502 with
        | FStar_Syntax_Syntax.Discriminator uu____7503 -> true
        | FStar_Syntax_Syntax.Projector uu____7504 -> true
        | FStar_Syntax_Syntax.RecordType uu____7507 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7512 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7517 -> false in
      let has_eq uu___111_7521 =
        match uu___111_7521 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7522 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7556 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7559 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7562 =
        let uu____7563 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___112_7565  ->
                  match uu___112_7565 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7566 -> false)) in
        FStar_All.pipe_right uu____7563 Prims.op_Negation in
      if uu____7562
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7576 =
            let uu____7577 =
              let uu____7580 =
                let uu____7581 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7581 msg in
              (uu____7580, r) in
            FStar_Errors.Error uu____7577 in
          raise uu____7576 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7589 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7601 =
            let uu____7602 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7602 in
          if uu____7601 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7606),uu____7607,uu____7608) ->
              ((let uu____7619 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7619
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7622 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7622
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7626 ->
              let uu____7631 =
                let uu____7632 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7632 in
              if uu____7631 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7636 ->
              let uu____7640 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7640 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7643 ->
              let uu____7646 =
                let uu____7647 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7647 in
              if uu____7646 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7651 ->
              let uu____7652 =
                let uu____7653 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7653 in
              if uu____7652 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7657 ->
              let uu____7658 =
                let uu____7659 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7659 in
              if uu____7658 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7663 ->
              let uu____7670 =
                let uu____7671 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7671 in
              if uu____7670 then err'1 () else ()
          | uu____7675 -> ()))
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
                          let uu____7742 =
                            let uu____7745 =
                              let uu____7746 =
                                let uu____7751 =
                                  let uu____7752 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7752 in
                                (uu____7751, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7746 in
                            FStar_Syntax_Syntax.mk uu____7745 in
                          uu____7742 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7778  ->
                                  match uu____7778 with
                                  | (x,imp) ->
                                      let uu____7785 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7785, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7789 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7789 in
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
                             let uu____7798 =
                               let uu____7799 =
                                 let uu____7800 =
                                   let uu____7801 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7802 =
                                     let uu____7803 =
                                       let uu____7804 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7804 in
                                     [uu____7803] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7801
                                     uu____7802 in
                                 uu____7800 None p in
                               FStar_Syntax_Util.b2t uu____7799 in
                             FStar_Syntax_Util.refine x uu____7798 in
                           let uu____7809 =
                             let uu___149_7810 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___149_7810.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___149_7810.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7809) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7821 =
                          FStar_List.map
                            (fun uu____7831  ->
                               match uu____7831 with
                               | (x,uu____7838) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7821 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7862  ->
                                match uu____7862 with
                                | (x,uu____7869) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7878 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7878)
                               ||
                               (let uu____7879 =
                                  let uu____7880 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7880.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7879) in
                           let quals =
                             let uu____7883 =
                               let uu____7885 =
                                 let uu____7887 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7887
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7890 =
                                 FStar_List.filter
                                   (fun uu___113_7892  ->
                                      match uu___113_7892 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7893 -> false) iquals in
                               FStar_List.append uu____7885 uu____7890 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7883 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7906 =
                                 let uu____7907 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7907 in
                               FStar_Syntax_Syntax.mk_Total uu____7906 in
                             let uu____7908 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7908 in
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
                           (let uu____7911 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7911
                            then
                              let uu____7912 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7912
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
                                             fun uu____7940  ->
                                               match uu____7940 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7958 =
                                                       let uu____7961 =
                                                         let uu____7962 =
                                                           let uu____7967 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7967,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7962 in
                                                       pos uu____7961 in
                                                     (uu____7958, b)
                                                   else
                                                     (let uu____7971 =
                                                        let uu____7974 =
                                                          let uu____7975 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7975 in
                                                        pos uu____7974 in
                                                      (uu____7971, b)))) in
                                   let pat_true =
                                     let uu____7987 =
                                       let uu____7990 =
                                         let uu____7991 =
                                           let uu____7999 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7999, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7991 in
                                       pos uu____7990 in
                                     (uu____7987, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____8021 =
                                       let uu____8024 =
                                         let uu____8025 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8025 in
                                       pos uu____8024 in
                                     (uu____8021, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____8034 =
                                     let uu____8037 =
                                       let uu____8038 =
                                         let uu____8054 =
                                           let uu____8056 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8057 =
                                             let uu____8059 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8059] in
                                           uu____8056 :: uu____8057 in
                                         (arg_exp, uu____8054) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8038 in
                                     FStar_Syntax_Syntax.mk uu____8037 in
                                   uu____8034 None p) in
                              let dd =
                                let uu____8070 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8070
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
                                let uu____8082 =
                                  let uu____8085 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____8085 in
                                let uu____8086 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____8082;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____8086
                                } in
                              let impl =
                                let uu____8090 =
                                  let uu____8091 =
                                    let uu____8097 =
                                      let uu____8099 =
                                        let uu____8100 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8100
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8099] in
                                    ((false, [lb]), uu____8097, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____8091 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8090;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____8115 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8115
                               then
                                 let uu____8116 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8116
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
                                fun uu____8136  ->
                                  match uu____8136 with
                                  | (a,uu____8140) ->
                                      let uu____8141 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8141 with
                                       | (field_name,uu____8145) ->
                                           let field_proj_tm =
                                             let uu____8147 =
                                               let uu____8148 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8148 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8147 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8162 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8171  ->
                                    match uu____8171 with
                                    | (x,uu____8176) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8178 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8178 with
                                         | (field_name,uu____8183) ->
                                             let t =
                                               let uu____8185 =
                                                 let uu____8186 =
                                                   let uu____8189 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8189 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8186 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8185 in
                                             let only_decl =
                                               ((let uu____8191 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____8191)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8192 =
                                                    let uu____8193 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8193.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8192) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8203 =
                                                   FStar_List.filter
                                                     (fun uu___114_8205  ->
                                                        match uu___114_8205
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8206 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8203
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___115_8214  ->
                                                         match uu___115_8214
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8215 ->
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
                                             ((let uu____8218 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8218
                                               then
                                                 let uu____8219 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8219
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
                                                           fun uu____8246  ->
                                                             match uu____8246
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8264
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8264,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8278
                                                                    =
                                                                    let uu____8281
                                                                    =
                                                                    let uu____8282
                                                                    =
                                                                    let uu____8287
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8287,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8282 in
                                                                    pos
                                                                    uu____8281 in
                                                                    (uu____8278,
                                                                    b))
                                                                   else
                                                                    (let uu____8291
                                                                    =
                                                                    let uu____8294
                                                                    =
                                                                    let uu____8295
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8295 in
                                                                    pos
                                                                    uu____8294 in
                                                                    (uu____8291,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8307 =
                                                     let uu____8310 =
                                                       let uu____8311 =
                                                         let uu____8319 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8319,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8311 in
                                                     pos uu____8310 in
                                                   let uu____8325 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8307, None,
                                                     uu____8325) in
                                                 let body =
                                                   let uu____8336 =
                                                     let uu____8339 =
                                                       let uu____8340 =
                                                         let uu____8356 =
                                                           let uu____8358 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8358] in
                                                         (arg_exp,
                                                           uu____8356) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8340 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8339 in
                                                   uu____8336 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8375 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8375
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
                                                   let uu____8381 =
                                                     let uu____8384 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8384 in
                                                   let uu____8385 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8381;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8385
                                                   } in
                                                 let impl =
                                                   let uu____8389 =
                                                     let uu____8390 =
                                                       let uu____8396 =
                                                         let uu____8398 =
                                                           let uu____8399 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8399
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8398] in
                                                       ((false, [lb]),
                                                         uu____8396, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8390 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8389;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8414 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8414
                                                  then
                                                    let uu____8415 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8415
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8162 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8449) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8452 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8452 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8465 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8465 with
                    | (formals,uu____8475) ->
                        let uu____8486 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8499 =
                                   let uu____8500 =
                                     let uu____8501 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8501 in
                                   FStar_Ident.lid_equals typ_lid uu____8500 in
                                 if uu____8499
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8511,uvs',tps,typ0,uu____8515,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8531 -> failwith "Impossible"
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
                        (match uu____8486 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8573 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8573 with
                              | (indices,uu____8583) ->
                                  let refine_domain =
                                    let uu____8595 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___116_8597  ->
                                              match uu___116_8597 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8598 -> true
                                              | uu____8603 -> false)) in
                                    if uu____8595
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___117_8610 =
                                      match uu___117_8610 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8612,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8619 -> None in
                                    let uu____8620 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8620 with
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
                                    let uu____8628 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8628 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8659  ->
                                               fun uu____8660  ->
                                                 match (uu____8659,
                                                         uu____8660)
                                                 with
                                                 | ((x,uu____8670),(x',uu____8672))
                                                     ->
                                                     let uu____8677 =
                                                       let uu____8682 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8682) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8677) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8683 -> []