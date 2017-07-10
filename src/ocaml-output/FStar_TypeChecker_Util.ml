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
        FStar_Syntax_Syntax.pos = uu____81;_} -> uv
    | uu____99 -> failwith "Impossible"
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
          let uu____122 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____122 with
          | FStar_Pervasives_Native.Some (uu____135::(tm,uu____137)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____177 ->
              let uu____184 = new_uvar_aux env k in
              (match uu____184 with
               | (t,u) ->
                   let g =
                     let uu___119_196 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____197 =
                       let uu____205 =
                         let uu____212 = as_uvar u in
                         (reason, env, uu____212, t, k, r) in
                       [uu____205] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_196.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_196.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_196.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____197
                     } in
                   let uu____225 =
                     let uu____229 =
                       let uu____232 = as_uvar u in (uu____232, r) in
                     [uu____229] in
                   (t, uu____225, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____252 =
        let uu____253 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____253 in
      if uu____252
      then
        let us =
          let uu____257 =
            let uu____259 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____270  ->
                 match uu____270 with
                 | (x,uu____274) -> FStar_Syntax_Print.uvar_to_string x)
              uu____259 in
          FStar_All.pipe_right uu____257 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____280 =
            let uu____281 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____281 in
          FStar_Errors.err r uu____280);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____291 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____291 with
    | FStar_Pervasives_Native.None  ->
        let uu____296 =
          let uu____297 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____298 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____297 uu____298 in
        failwith uu____296
    | FStar_Pervasives_Native.Some tk -> tk
let force_sort s =
  let uu____315 =
    let uu____318 = force_sort' s in FStar_Syntax_Syntax.mk uu____318 in
  uu____315 FStar_Pervasives_Native.None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.typ,
        Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____337  ->
      match uu____337 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____344;
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
                   let uu____376 =
                     let uu____377 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____377.FStar_Syntax_Syntax.n in
                   match uu____376 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____382 = FStar_Syntax_Util.type_u () in
                       (match uu____382 with
                        | (k,uu____388) ->
                            let t2 =
                              let uu____390 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____390
                                FStar_Pervasives_Native.fst in
                            ((let uu___120_396 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_396.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_396.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____397 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____422) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____429) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____475) ->
                       let uu____488 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____525  ->
                                 fun uu____526  ->
                                   match (uu____525, uu____526) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____568 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____568 with
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
                            let uu____629 = aux must_check_ty1 scope body in
                            (match uu____629 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____646 =
                                         FStar_Options.ml_ish () in
                                       if uu____646
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____653 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____653
                                   then
                                     let uu____654 =
                                       FStar_Range.string_of_range r in
                                     let uu____655 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____656 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____654 uu____655 uu____656
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____664 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____672 =
                            let uu____675 =
                              let uu____676 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____676
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____675 in
                          (uu____672, false)) in
                 let uu____683 =
                   let uu____688 = t_binders env in aux false uu____688 e in
                 match uu____683 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____705 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____705
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____709 =
                                let uu____710 =
                                  let uu____713 =
                                    let uu____714 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____714 in
                                  (uu____713, rng) in
                                FStar_Errors.Error uu____710 in
                              raise uu____709)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____721 ->
               let uu____722 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____722 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____793) ->
              let uu____798 = FStar_Syntax_Util.type_u () in
              (match uu____798 with
               | (k,uu____811) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_814 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_814.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_814.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____815 =
                     let uu____818 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____818 t in
                   (match uu____815 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_832 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___122_832.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____838 = FStar_Syntax_Util.type_u () in
              (match uu____838 with
               | (t,uu____851) ->
                   let x1 =
                     let uu___123_853 = x in
                     let uu____854 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_853.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_853.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____854
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
              let uu____872 = FStar_Syntax_Util.type_u () in
              (match uu____872 with
               | (t,uu____885) ->
                   let x1 =
                     let uu___124_887 = x in
                     let uu____888 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_887.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_887.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____888
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____914 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____987  ->
                        fun uu____988  ->
                          match (uu____987, uu____988) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1087 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1087 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____914 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1195 =
                       let uu____1198 =
                         let uu____1199 =
                           let uu____1204 =
                             let uu____1207 =
                               let uu____1208 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1209 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1208
                                 uu____1209 in
                             uu____1207 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1204,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1199 in
                       FStar_Syntax_Syntax.mk uu____1198 in
                     uu____1195 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1226 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1232 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1238 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1226, uu____1232, uu____1238, env2, e,
                     (let uu___125_1251 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___125_1251.FStar_Syntax_Syntax.p)
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
                  (fun uu____1306  ->
                     match uu____1306 with
                     | (p2,imp) ->
                         let uu____1317 = elaborate_pat env1 p2 in
                         (uu____1317, imp)) pats in
              let uu____1320 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1320 with
               | (uu____1324,t) ->
                   let uu____1326 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1326 with
                    | (f,uu____1336) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1403::uu____1404) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1430::uu____1431,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1474  ->
                                      match uu____1474 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1490 =
                                                   let uu____1492 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____1492 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1490
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1494 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1494, true)
                                           | uu____1497 ->
                                               let uu____1499 =
                                                 let uu____1500 =
                                                   let uu____1503 =
                                                     let uu____1504 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1504 in
                                                   (uu____1503,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1500 in
                                               raise uu____1499)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1544,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____1545))
                                   when p_imp ->
                                   let uu____1547 = aux formals' pats' in
                                   (p2, true) :: uu____1547
                               | (uu____1556,FStar_Pervasives_Native.Some
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
                                   let uu____1562 = aux formals' pats2 in
                                   (p3, true) :: uu____1562
                               | (uu____1571,imp) ->
                                   let uu____1575 =
                                     let uu____1579 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1579) in
                                   let uu____1581 = aux formals' pats' in
                                   uu____1575 :: uu____1581) in
                        let uu___126_1589 = p1 in
                        let uu____1591 =
                          let uu____1592 =
                            let uu____1599 = aux f pats1 in (fv, uu____1599) in
                          FStar_Syntax_Syntax.Pat_cons uu____1592 in
                        {
                          FStar_Syntax_Syntax.v = uu____1591;
                          FStar_Syntax_Syntax.p =
                            (uu___126_1589.FStar_Syntax_Syntax.p)
                        }))
          | uu____1608 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1631 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1631 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1661 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1661 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____1674 =
                     let uu____1675 =
                       let uu____1678 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1678, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1675 in
                   raise uu____1674
               | uu____1687 -> (b, a, w, arg, p3)) in
        let uu____1692 = one_pat true env p in
        match uu____1692 with
        | (b,uu____1706,uu____1707,tm,p1) -> (b, tm, p1)
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
          | (uu____1745,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1747)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1752,FStar_Syntax_Syntax.Tm_constant uu____1753) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1757 =
                    let uu____1758 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1759 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1758 uu____1759 in
                  failwith uu____1757)
               else ();
               (let uu____1762 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1762
                then
                  let uu____1763 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1764 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1763
                    uu____1764
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_1768 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_1768.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_1768.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1772 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1772
                then
                  let uu____1773 =
                    let uu____1774 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1775 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1774 uu____1775 in
                  failwith uu____1773
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_1779 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1779.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1779.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1781),uu____1782) ->
              let s = force_sort e1 in
              let x1 =
                let uu___129_1791 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___129_1791.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___129_1791.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1802 =
                  let uu____1803 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1803 in
                if uu____1802
                then
                  let uu____1804 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1804
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1816;
                FStar_Syntax_Syntax.pos = uu____1817;_},args))
              ->
              ((let uu____1841 =
                  let uu____1842 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1842 Prims.op_Negation in
                if uu____1841
                then
                  let uu____1843 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1843
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1924)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1968) ->
                           let x =
                             let uu____1984 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____1984 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____1995) ->
                           let pat =
                             let uu____2010 = aux argpat e2 in
                             let uu____2011 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2010, uu____2011) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2014 ->
                      let uu____2027 =
                        let uu____2028 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2029 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2028 uu____2029 in
                      failwith uu____2027 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2037;
                     FStar_Syntax_Syntax.pos = uu____2038;_},uu____2039);
                FStar_Syntax_Syntax.tk = uu____2040;
                FStar_Syntax_Syntax.pos = uu____2041;_},args))
              ->
              ((let uu____2068 =
                  let uu____2069 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2069 Prims.op_Negation in
                if uu____2068
                then
                  let uu____2070 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2070
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2151)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2195) ->
                           let x =
                             let uu____2211 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p)) uu____2211 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2222) ->
                           let pat =
                             let uu____2237 = aux argpat e2 in
                             let uu____2238 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2237, uu____2238) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2241 ->
                      let uu____2254 =
                        let uu____2255 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2256 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2255 uu____2256 in
                      failwith uu____2254 in
                match_args [] args argpats))
          | uu____2261 ->
              let uu____2264 =
                let uu____2265 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2266 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2267 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2265 uu____2266 uu____2267 in
              failwith uu____2264 in
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
    let pat_as_arg uu____2296 =
      match uu____2296 with
      | (p,i) ->
          let uu____2306 = decorated_pattern_as_term p in
          (match uu____2306 with
           | (vars,te) ->
               let uu____2319 =
                 let uu____2322 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2322) in
               (vars, uu____2319)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2330 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2330)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2333 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2333)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2336 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2336)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2348 =
          let uu____2356 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2356 FStar_List.unzip in
        (match uu____2348 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2413 =
               let uu____2414 =
                 let uu____2415 =
                   let uu____2425 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2425, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2415 in
               mk1 uu____2414 in
             (vars1, uu____2413))
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
      | (wp,uu____2455)::[] -> wp
      | uu____2468 ->
          let uu____2474 =
            let uu____2475 =
              let uu____2476 =
                FStar_List.map
                  (fun uu____2483  ->
                     match uu____2483 with
                     | (x,uu____2487) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2476 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2475 in
          failwith uu____2474 in
    let uu____2491 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2491, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2508 = destruct_comp c in
        match uu____2508 with
        | (u,uu____2513,wp) ->
            let uu____2515 =
              let uu____2521 =
                let uu____2522 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2522 in
              [uu____2521] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2515;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2535 =
          let uu____2539 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2540 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2539 uu____2540 in
        match uu____2535 with | (m,uu____2542,uu____2543) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2556 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2556
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
        let uu____2584 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2584 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2606 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2606 with
             | (a,kwp) ->
                 let uu____2623 = destruct_comp m1 in
                 let uu____2627 = destruct_comp m2 in
                 ((md, a, kwp), uu____2623, uu____2627))
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
            let uu____2684 =
              let uu____2685 =
                let uu____2691 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2691] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2685;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2684
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
      let uu___130_2738 = lc in
      let uu____2739 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___130_2738.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2739;
        FStar_Syntax_Syntax.cflags =
          (uu___130_2738.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2744  ->
             let uu____2745 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2745)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2750 =
      let uu____2751 = FStar_Syntax_Subst.compress t in
      uu____2751.FStar_Syntax_Syntax.n in
    match uu____2750 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2754 -> true
    | uu____2762 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2777 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2777
        then c
        else
          (let uu____2779 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2779
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2815 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2815] in
                       let us =
                         let uu____2818 =
                           let uu____2820 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2820] in
                         u_res :: uu____2818 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2824 =
                         let uu____2825 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2826 =
                           let uu____2827 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2828 =
                             let uu____2830 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2831 =
                               let uu____2833 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2833] in
                             uu____2830 :: uu____2831 in
                           uu____2827 :: uu____2828 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2825 uu____2826 in
                       uu____2824 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2839 = destruct_comp c1 in
              match uu____2839 with
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
        let close1 uu____2865 =
          let uu____2866 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2866 in
        let uu___131_2867 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_2867.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_2867.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_2867.FStar_Syntax_Syntax.cflags);
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
          let uu____2881 =
            let uu____2882 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2882 in
          if uu____2881
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2887 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2887
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2889 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____2889 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2895 =
                        let uu____2896 =
                          let uu____2897 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2898 =
                            let uu____2899 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2900 =
                              let uu____2902 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2902] in
                            uu____2899 :: uu____2900 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2897 uu____2898 in
                        uu____2896
                          (FStar_Pervasives_Native.Some
                             (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2895) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2908 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2908
         then
           let uu____2909 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2910 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2911 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2909
             uu____2910 uu____2911
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
          fun uu____2933  ->
            match uu____2933 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2943 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2943
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____2946 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____2948 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2949 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2946 uu____2948 bstr uu____2949
                  else ());
                 (let bind_it uu____2954 =
                    let uu____2955 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2955
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____2965 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____2965
                        then
                          let uu____2966 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____2968 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____2969 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2970 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____2971 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____2966 uu____2968 uu____2969 uu____2970
                            uu____2971
                        else ());
                       (let try_simplify uu____2982 =
                          let aux uu____2992 =
                            let uu____2993 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2993
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____3012 ->
                                  let uu____3013 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3013
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3032 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3032
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____3068 =
                                  let uu____3071 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3071, reason) in
                                FStar_Util.Inl uu____3068
                            | uu____3074 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3089 =
                              let uu____3090 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3090.FStar_Syntax_Syntax.n in
                            match uu____3089 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3094) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3100 -> c in
                          let uu____3101 =
                            let uu____3102 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3102 in
                          if uu____3101
                          then
                            let uu____3110 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3110
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3124 =
                                  let uu____3125 =
                                    let uu____3128 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3128) in
                                  FStar_Errors.Error uu____3125 in
                                raise uu____3124))
                          else
                            (let uu____3136 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3136
                             then subst_c2 "both total"
                             else
                               (let uu____3144 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3144
                                then
                                  let uu____3151 =
                                    let uu____3154 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3154, "both gtot") in
                                  FStar_Util.Inl uu____3151
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____3170 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3172 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3172) in
                                       if uu____3170
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___132_3181 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___132_3181.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___132_3181.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3182 =
                                           let uu____3185 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3185, "c1 Tot") in
                                         FStar_Util.Inl uu____3182
                                       else aux ()
                                   | uu____3189 -> aux ()))) in
                        let uu____3194 = try_simplify () in
                        match uu____3194 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3212 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3212
                              then
                                let uu____3213 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3214 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3215 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3213 uu____3214 uu____3215
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3222 = lift_and_destruct env c1 c2 in
                            (match uu____3222 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3256 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3256]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____3258 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3258] in
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
                                   let uu____3274 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3275 =
                                     let uu____3277 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3278 =
                                       let uu____3280 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3281 =
                                         let uu____3283 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3284 =
                                           let uu____3286 =
                                             let uu____3287 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3287 in
                                           [uu____3286] in
                                         uu____3283 :: uu____3284 in
                                       uu____3280 :: uu____3281 in
                                     uu____3277 :: uu____3278 in
                                   uu____3274 :: uu____3275 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3292 =
                                     let uu____3293 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3293
                                       wp_args in
                                   uu____3292 FStar_Pervasives_Native.None
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
              let uu____3344 =
                let uu____3345 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3345 in
              if uu____3344
              then f
              else (let uu____3347 = reason1 () in label uu____3347 r f)
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
            let uu___133_3361 = g in
            let uu____3362 =
              let uu____3363 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3363 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3362;
              FStar_TypeChecker_Env.deferred =
                (uu___133_3361.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_3361.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_3361.FStar_TypeChecker_Env.implicits)
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
      | uu____3375 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3395 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3399 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3399
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3406 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3406
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3411 = destruct_comp c1 in
                    match uu____3411 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3424 =
                            let uu____3425 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3426 =
                              let uu____3427 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3428 =
                                let uu____3430 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3431 =
                                  let uu____3433 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3433] in
                                uu____3430 :: uu____3431 in
                              uu____3427 :: uu____3428 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3425
                              uu____3426 in
                          uu____3424 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___134_3438 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___134_3438.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___134_3438.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___134_3438.FStar_Syntax_Syntax.cflags);
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
            let uu____3470 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3470
            then (lc, g0)
            else
              ((let uu____3475 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3475
                then
                  let uu____3476 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3477 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3476 uu____3477
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3484  ->
                          match uu___100_3484 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3486 -> [])) in
                let strengthen uu____3492 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3500 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3500 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3507 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3509 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3509) in
                           if uu____3507
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3516 =
                                 let uu____3517 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3517 in
                               FStar_Syntax_Util.comp_set_flags uu____3516
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3522 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3522
                           then
                             let uu____3523 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3524 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3523 uu____3524
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3527 = destruct_comp c2 in
                           match uu____3527 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3540 =
                                   let uu____3541 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3542 =
                                     let uu____3543 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3544 =
                                       let uu____3546 =
                                         let uu____3547 =
                                           let uu____3548 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3548 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3547 in
                                       let uu____3549 =
                                         let uu____3551 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3551] in
                                       uu____3546 :: uu____3549 in
                                     uu____3543 :: uu____3544 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3541
                                     uu____3542 in
                                 uu____3540 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3557 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3557
                                 then
                                   let uu____3558 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3558
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3561 =
                  let uu___135_3562 = lc in
                  let uu____3563 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3564 =
                    let uu____3566 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3568 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3568) in
                    if uu____3566 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3563;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___135_3562.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3564;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3561,
                  (let uu___136_3572 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___136_3572.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___136_3572.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___136_3572.FStar_TypeChecker_Env.implicits)
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
        let uu____3590 =
          let uu____3593 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3594 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3593, uu____3594) in
        match uu____3590 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3603 =
                let uu____3604 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3605 =
                  let uu____3606 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3607 =
                    let uu____3609 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3609] in
                  uu____3606 :: uu____3607 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3604 uu____3605 in
              uu____3603 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3617 =
                let uu____3618 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3619 =
                  let uu____3620 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3621 =
                    let uu____3623 =
                      let uu____3624 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3624 in
                    let uu____3625 =
                      let uu____3627 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3627] in
                    uu____3623 :: uu____3625 in
                  uu____3620 :: uu____3621 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3618 uu____3619 in
              uu____3617 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3635 =
                let uu____3636 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3637 =
                  let uu____3638 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3639 =
                    let uu____3641 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3642 =
                      let uu____3644 =
                        let uu____3645 =
                          let uu____3646 =
                            let uu____3647 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3647] in
                          FStar_Syntax_Util.abs uu____3646 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3645 in
                      [uu____3644] in
                    uu____3641 :: uu____3642 in
                  uu____3638 :: uu____3639 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3636 uu____3637 in
              uu____3635 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3656 = FStar_TypeChecker_Env.get_range env in
              bind uu____3656 env FStar_Pervasives_Native.None
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
          let comp uu____3678 =
            let uu____3679 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3679
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3682 =
                 let uu____3695 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3696 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3695 uu____3696 in
               match uu____3682 with
               | ((md,uu____3698,uu____3699),(u_res_t,res_t,wp_then),
                  (uu____3703,uu____3704,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3733 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3734 =
                       let uu____3735 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3736 =
                         let uu____3737 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3738 =
                           let uu____3740 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3741 =
                             let uu____3743 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3744 =
                               let uu____3746 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3746] in
                             uu____3743 :: uu____3744 in
                           uu____3740 :: uu____3741 in
                         uu____3737 :: uu____3738 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3735 uu____3736 in
                     uu____3734 FStar_Pervasives_Native.None uu____3733 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3754 =
                     let uu____3755 = FStar_Options.split_cases () in
                     uu____3755 > (Prims.parse_int "0") in
                   if uu____3754
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3761 =
                          let uu____3762 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3763 =
                            let uu____3764 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3765 =
                              let uu____3767 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3767] in
                            uu____3764 :: uu____3765 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3762 uu____3763 in
                        uu____3761 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3772 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3772;
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
      let uu____3781 =
        let uu____3782 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3782 in
      FStar_Syntax_Syntax.fvar uu____3781 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3809  ->
                 match uu____3809 with
                 | (uu____3812,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____3817 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3819 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3819
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3839 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3840 =
                 let uu____3841 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3842 =
                   let uu____3843 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3844 =
                     let uu____3846 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3847 =
                       let uu____3849 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3850 =
                         let uu____3852 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3852] in
                       uu____3849 :: uu____3850 in
                     uu____3846 :: uu____3847 in
                   uu____3843 :: uu____3844 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3841 uu____3842 in
               uu____3840 FStar_Pervasives_Native.None uu____3839 in
             let default_case =
               let post_k =
                 let uu____3861 =
                   let uu____3865 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3865] in
                 let uu____3866 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3861 uu____3866 in
               let kwp =
                 let uu____3872 =
                   let uu____3876 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3876] in
                 let uu____3877 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3872 uu____3877 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____3882 =
                   let uu____3883 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3883] in
                 let uu____3884 =
                   let uu____3885 =
                     let uu____3888 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3888 in
                   let uu____3889 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____3885 uu____3889 in
                 FStar_Syntax_Util.abs uu____3882 uu____3884
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
                 (fun uu____3911  ->
                    fun celse  ->
                      match uu____3911 with
                      | (g,cthen) ->
                          let uu____3917 =
                            let uu____3930 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3930 celse in
                          (match uu____3917 with
                           | ((md,uu____3932,uu____3933),(uu____3934,uu____3935,wp_then),
                              (uu____3937,uu____3938,wp_else)) ->
                               let uu____3949 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3949 []))
                 lcases default_case in
             let uu____3950 =
               let uu____3951 = FStar_Options.split_cases () in
               uu____3951 > (Prims.parse_int "0") in
             if uu____3950
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3955 = destruct_comp comp1 in
                match uu____3955 with
                | (uu____3959,uu____3960,wp) ->
                    let wp1 =
                      let uu____3965 =
                        let uu____3966 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3967 =
                          let uu____3968 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3969 =
                            let uu____3971 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3971] in
                          uu____3968 :: uu____3969 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3966 uu____3967 in
                      uu____3965 FStar_Pervasives_Native.None
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
          let uu____3990 =
            ((let uu____3993 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____3993) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3995 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____3995) in
          if uu____3990
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4003 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4007 =
            (let uu____4010 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4010) || env.FStar_TypeChecker_Env.lax in
          if uu____4007
          then c
          else
            (let uu____4014 = FStar_Syntax_Util.is_partial_return c in
             if uu____4014
             then c
             else
               (let uu____4018 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4018
                then
                  let uu____4021 =
                    let uu____4022 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4022 in
                  (if uu____4021
                   then
                     let uu____4025 =
                       let uu____4026 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4027 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4026 uu____4027 in
                     failwith uu____4025
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4032 =
                        let uu____4033 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4033 in
                      if uu____4032
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___137_4038 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___137_4038.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___137_4038.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___137_4038.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4049 =
                       let uu____4052 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4052
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4049 in
                   let eq1 =
                     let uu____4056 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4056 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4058 =
                     let uu____4059 =
                       let uu____4064 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____4064.FStar_Syntax_Syntax.comp in
                     uu____4059 () in
                   FStar_Syntax_Util.comp_set_flags uu____4058 flags))) in
        let uu___138_4066 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___138_4066.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___138_4066.FStar_Syntax_Syntax.res_typ);
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
          let uu____4089 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4089 with
          | FStar_Pervasives_Native.None  ->
              let uu____4094 =
                let uu____4095 =
                  let uu____4098 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4099 = FStar_TypeChecker_Env.get_range env in
                  (uu____4098, uu____4099) in
                FStar_Errors.Error uu____4095 in
              raise uu____4094
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
            let uu____4129 =
              let uu____4130 = FStar_Syntax_Subst.compress t2 in
              uu____4130.FStar_Syntax_Syntax.n in
            match uu____4129 with
            | FStar_Syntax_Syntax.Tm_type uu____4133 -> true
            | uu____4134 -> false in
          let uu____4135 =
            let uu____4136 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4136.FStar_Syntax_Syntax.n in
          match uu____4135 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4142 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____4149 =
                  let uu____4150 =
                    let uu____4151 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4151 in
                  (FStar_Pervasives_Native.None, uu____4150) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____4149 in
              let e1 =
                let uu____4160 =
                  let uu____4161 =
                    let uu____4162 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4162] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4161 in
                uu____4160
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4169 -> (e, lc)
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
              (let uu____4196 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4196 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4209 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4221 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4221, false)
            else
              (let uu____4225 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4225, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____4231) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___139_4235 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___139_4235.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___139_4235.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___139_4235.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____4239 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4239 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_4244 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_4244.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_4244.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___140_4244.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_4247 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_4247.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_4247.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_4247.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4253 =
                     let uu____4254 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4254
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____4259 =
                          let uu____4260 = FStar_Syntax_Subst.compress f1 in
                          uu____4260.FStar_Syntax_Syntax.n in
                        match uu____4259 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4265,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4267;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4268;_},uu____4269)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_4282 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_4282.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_4282.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___142_4282.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4283 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4288 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4288
                              then
                                let uu____4289 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4290 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4291 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4292 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4289 uu____4290 uu____4291 uu____4292
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4295 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____4295 with
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
                                  let uu____4306 = destruct_comp ct in
                                  (match uu____4306 with
                                   | (u_t,uu____4313,uu____4314) ->
                                       let wp =
                                         let uu____4318 =
                                           let uu____4319 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4320 =
                                             let uu____4321 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4322 =
                                               let uu____4324 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4324] in
                                             uu____4321 :: uu____4322 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4319 uu____4320 in
                                         uu____4318
                                           (FStar_Pervasives_Native.Some
                                              (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4330 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4330 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4340 =
                                             let uu____4341 =
                                               let uu____4342 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4342] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4341 in
                                           uu____4340
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4348 =
                                         let uu____4351 =
                                           FStar_All.pipe_left
                                             (fun _0_39  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4362 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4363 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4351
                                           uu____4362 e cret uu____4363 in
                                       (match uu____4348 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___143_4369 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___143_4369.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___143_4369.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4371 =
                                                let uu____4372 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4372 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____4371
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4382 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4382
                                              then
                                                let uu____4383 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4383
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4390  ->
                             match uu___101_4390 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4392 -> [])) in
                   let lc1 =
                     let uu___144_4394 = lc in
                     let uu____4395 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4395;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___145_4397 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___145_4397.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___145_4397.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___145_4397.FStar_TypeChecker_Env.implicits)
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
        let uu____4419 =
          let uu____4420 =
            let uu____4421 =
              let uu____4422 =
                let uu____4423 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4423 in
              [uu____4422] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4421 in
          uu____4420 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4419 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4432 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4432
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4443 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4452 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4469)::(ens,uu____4471)::uu____4472 ->
                    let uu____4494 =
                      let uu____4496 = norm req in
                      FStar_Pervasives_Native.Some uu____4496 in
                    let uu____4497 =
                      let uu____4498 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4498 in
                    (uu____4494, uu____4497)
                | uu____4500 ->
                    let uu____4506 =
                      let uu____4507 =
                        let uu____4510 =
                          let uu____4511 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4511 in
                        (uu____4510, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4507 in
                    raise uu____4506)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4521)::uu____4522 ->
                    let uu____4536 =
                      let uu____4539 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____4539 in
                    (match uu____4536 with
                     | (us_r,uu____4556) ->
                         let uu____4557 =
                           let uu____4560 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____4560 in
                         (match uu____4557 with
                          | (us_e,uu____4577) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4580 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4580
                                  us_r in
                              let as_ens =
                                let uu____4582 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4582
                                  us_e in
                              let req =
                                let uu____4586 =
                                  let uu____4587 =
                                    let uu____4588 =
                                      let uu____4595 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4595] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4588 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4587 in
                                uu____4586
                                  (FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4611 =
                                  let uu____4612 =
                                    let uu____4613 =
                                      let uu____4620 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4620] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____4613 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4612 in
                                uu____4611 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4633 =
                                let uu____4635 = norm req in
                                FStar_Pervasives_Native.Some uu____4635 in
                              let uu____4636 =
                                let uu____4637 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4637 in
                              (uu____4633, uu____4636)))
                | uu____4639 -> failwith "Impossible"))
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
      (let uu____4661 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4661
       then
         let uu____4662 = FStar_Syntax_Print.term_to_string tm in
         let uu____4663 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4662 uu____4663
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
        (let uu____4687 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4687
         then
           let uu____4688 = FStar_Syntax_Print.term_to_string tm in
           let uu____4689 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4688
             uu____4689
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4695 =
      let uu____4696 =
        let uu____4697 = FStar_Syntax_Subst.compress t in
        uu____4697.FStar_Syntax_Syntax.n in
      match uu____4696 with
      | FStar_Syntax_Syntax.Tm_app uu____4700 -> false
      | uu____4710 -> true in
    if uu____4695
    then t
    else
      (let uu____4712 = FStar_Syntax_Util.head_and_args t in
       match uu____4712 with
       | (head1,args) ->
           let uu____4738 =
             let uu____4739 =
               let uu____4740 = FStar_Syntax_Subst.compress head1 in
               uu____4740.FStar_Syntax_Syntax.n in
             match uu____4739 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4743 -> false in
           if uu____4738
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____4759 ->
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
             let uu____4790 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4790 with
             | (formals,uu____4799) ->
                 let n_implicits =
                   let uu____4811 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4851  ->
                             match uu____4851 with
                             | (uu____4855,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____4811 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4930 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4930 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4951 =
                     let uu____4952 =
                       let uu____4955 =
                         let uu____4956 = FStar_Util.string_of_int n_expected in
                         let uu____4963 = FStar_Syntax_Print.term_to_string e in
                         let uu____4964 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4956 uu____4963 uu____4964 in
                       let uu____4971 = FStar_TypeChecker_Env.get_range env in
                       (uu____4955, uu____4971) in
                     FStar_Errors.Error uu____4952 in
                   raise uu____4951
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___102_4989 =
             match uu___102_4989 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5008 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5008 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_40,uu____5069) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5091,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5110 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5110 with
                           | (v1,uu____5131,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5141 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5141 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5190 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5190)))
                      | (uu____5204,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5228 =
                      let uu____5242 = inst_n_binders t in
                      aux [] uu____5242 bs1 in
                    (match uu____5228 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5280) -> (e, torig, guard)
                          | (uu____5296,[]) when
                              let uu____5312 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5312 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5313 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5332 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  (FStar_Pervasives_Native.Some
                                     (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5345 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5352 =
      let uu____5354 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5354
        (FStar_List.map
           (fun u  ->
              let uu____5361 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5361 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5352 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5375 = FStar_Util.set_is_empty x in
      if uu____5375
      then []
      else
        (let s =
           let uu____5380 =
             let uu____5382 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5382 in
           FStar_All.pipe_right uu____5380 FStar_Util.set_elements in
         (let uu____5387 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5387
          then
            let uu____5388 =
              let uu____5389 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5389 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5388
          else ());
         (let r =
            let uu____5394 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____5394 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5406 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5406
                     then
                       let uu____5407 =
                         let uu____5408 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5408 in
                       let uu____5409 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5410 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5407 uu____5409 uu____5410
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
        let uu____5429 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5429 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_5459 =
  match uu___103_5459 with
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
        | ([],uu____5502) -> generalized_univ_names
        | (uu____5506,[]) -> explicit_univ_names
        | uu____5510 ->
            let uu____5515 =
              let uu____5516 =
                let uu____5519 =
                  let uu____5520 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5520 in
                (uu____5519, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5516 in
            raise uu____5515
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
      (let uu____5536 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5536
       then
         let uu____5537 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5537
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5542 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5542
        then
          let uu____5543 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5543
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____5549 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5549))
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
      let uu____5581 =
        let uu____5582 =
          FStar_Util.for_all
            (fun uu____5590  ->
               match uu____5590 with
               | (uu____5595,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5582 in
      if uu____5581
      then FStar_Pervasives_Native.None
      else
        (let norm c =
           (let uu____5618 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5618
            then
              let uu____5619 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5619
            else ());
           (let c1 =
              let uu____5622 = FStar_TypeChecker_Env.should_verify env in
              if uu____5622
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
            (let uu____5625 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5625
             then
               let uu____5626 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5626
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5642 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5642 FStar_Util.set_elements in
         let uu____5656 =
           let uu____5668 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5717  ->
                     match uu____5717 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____5751 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____5751
                           then
                             let uu____5752 =
                               let uu____5753 =
                                 let uu____5755 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____5755
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____5753
                                 (FStar_String.concat ", ") in
                             let uu____5770 =
                               let uu____5771 =
                                 let uu____5773 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____5773
                                   (FStar_List.map
                                      (fun uu____5790  ->
                                         match uu____5790 with
                                         | (u,t2) ->
                                             let uu____5795 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____5796 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____5795 uu____5796)) in
                               FStar_All.pipe_right uu____5771
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____5752 uu____5770
                           else ());
                          (let univs2 =
                             let uu____5801 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____5816  ->
                                    match uu____5816 with
                                    | (uu____5821,t2) ->
                                        let uu____5823 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____5823) univs1 uu____5801 in
                           let uvs = gen_uvars uvt in
                           (let uu____5830 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____5830
                            then
                              let uu____5831 =
                                let uu____5832 =
                                  let uu____5834 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____5834
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____5832
                                  (FStar_String.concat ", ") in
                              let uu____5849 =
                                let uu____5850 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____5863  ->
                                          match uu____5863 with
                                          | (u,t2) ->
                                              let uu____5868 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____5869 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____5868 uu____5869)) in
                                FStar_All.pipe_right uu____5850
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____5831 uu____5849
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____5668 FStar_List.unzip in
         match uu____5656 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5938 = FStar_List.hd univs1 in
               let uu____5941 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____5954 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____5954
                      then out
                      else
                        (let uu____5957 =
                           let uu____5958 =
                             let uu____5961 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____5961) in
                           FStar_Errors.Error uu____5958 in
                         raise uu____5957)) uu____5938 uu____5941 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5966 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5966
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
                      (fun uu____6007  ->
                         match uu____6007 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6051  ->
                                       match uu____6051 with
                                       | (u,k) ->
                                           let uu____6059 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6059 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6065;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6066;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6071,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6073;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6074;_},uu____6075);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6076;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6077;_}
                                                ->
                                                (a,
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Pervasives_Native.Some
                                                uu____6093 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6097 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta;
                                                    FStar_TypeChecker_Normalize.Exclude
                                                      FStar_TypeChecker_Normalize.Zeta]
                                                    env k in
                                                let uu____6100 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6100 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6124 =
                                                         let uu____6126 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              FStar_Pervasives_Native.Some
                                                                _0_41)
                                                           uu____6126 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6124 kres in
                                                     let t =
                                                       let uu____6129 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6129
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (FStar_Pervasives_Native.Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6132 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____6150 ->
                                   let uu____6158 = (e, c) in
                                   (match uu____6158 with
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
                                          let uu____6170 =
                                            let uu____6171 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6171.FStar_Syntax_Syntax.n in
                                          match uu____6170 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6188 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6188 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6198 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____6200 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6200)) in
                             (match uu____6132 with
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
      (let uu____6240 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6240
       then
         let uu____6241 =
           let uu____6242 =
             FStar_List.map
               (fun uu____6251  ->
                  match uu____6251 with
                  | (lb,uu____6256,uu____6257) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6242 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6241
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6271  ->
              match uu____6271 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6286 =
           let uu____6293 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6313  ->
                     match uu____6313 with | (uu____6319,e,c) -> (e, c))) in
           gen env uu____6293 in
         match uu____6286 with
         | FStar_Pervasives_Native.None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6355  ->
                     match uu____6355 with | (l,t,c) -> (l, [], t, c)))
         | FStar_Pervasives_Native.Some ecs ->
             FStar_List.map2
               (fun uu____6408  ->
                  fun uu____6409  ->
                    match (uu____6408, uu____6409) with
                    | ((l,uu____6442,uu____6443),(us,e,c)) ->
                        ((let uu____6469 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6469
                          then
                            let uu____6470 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6471 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6472 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6473 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6470 uu____6471 uu____6472 uu____6473
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6499  ->
              match uu____6499 with
              | (l,generalized_univs,t,c) ->
                  let uu____6517 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6517, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6554 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6554 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____6558 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____6558) in
          let is_var e1 =
            let uu____6564 =
              let uu____6565 = FStar_Syntax_Subst.compress e1 in
              uu____6565.FStar_Syntax_Syntax.n in
            match uu____6564 with
            | FStar_Syntax_Syntax.Tm_name uu____6568 -> true
            | uu____6569 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___146_6589 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___146_6589.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___146_6589.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      }))
                  (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6590 ->
                let uu___147_6591 = e2 in
                let uu____6592 =
                  FStar_Util.mk_ref
                    (FStar_Pervasives_Native.Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___147_6591.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6592;
                  FStar_Syntax_Syntax.pos =
                    (uu___147_6591.FStar_Syntax_Syntax.pos)
                } in
          let env2 =
            let uu___148_6599 = env1 in
            let uu____6600 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_6599.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_6599.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_6599.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_6599.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_6599.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_6599.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_6599.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_6599.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_6599.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_6599.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_6599.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_6599.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_6599.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_6599.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_6599.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6600;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_6599.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_6599.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_6599.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_6599.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_6599.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_6599.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_6599.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_6599.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___148_6599.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___148_6599.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___148_6599.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6601 = check env2 t1 t2 in
          match uu____6601 with
          | FStar_Pervasives_Native.None  ->
              let uu____6605 =
                let uu____6606 =
                  let uu____6609 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6610 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6609, uu____6610) in
                FStar_Errors.Error uu____6606 in
              raise uu____6605
          | FStar_Pervasives_Native.Some g ->
              ((let uu____6615 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6615
                then
                  let uu____6616 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6616
                else ());
               (let uu____6618 = decorate e t2 in (uu____6618, g)))
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
        let uu____6645 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6645
        then
          let uu____6648 = discharge g1 in
          let uu____6649 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6648, uu____6649)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6661 =
               let uu____6662 =
                 let uu____6663 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6663 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6662
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6661
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6665 = destruct_comp c1 in
           match uu____6665 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6677 = FStar_TypeChecker_Env.get_range env in
                 let uu____6678 =
                   let uu____6679 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6680 =
                     let uu____6681 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6682 =
                       let uu____6684 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6684] in
                     uu____6681 :: uu____6682 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6679 uu____6680 in
                 uu____6678
                   (FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6677 in
               ((let uu____6690 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6690
                 then
                   let uu____6691 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6691
                 else ());
                (let g2 =
                   let uu____6694 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6694 in
                 let uu____6695 = discharge g2 in
                 let uu____6696 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6695, uu____6696))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6722 =
        match uu___104_6722 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6728)::[] -> f fst1
        | uu____6741 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6746 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6746
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6755 =
          let uu____6758 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6758 in
        FStar_All.pipe_right uu____6755
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6769 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6769
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_6783 =
        match uu___105_6783 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6789)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6804)::[] ->
            let uu____6825 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6825
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6830 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6837 =
          let uu____6842 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____6842) in
        let uu____6847 =
          let uu____6853 =
            let uu____6858 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____6858) in
          let uu____6863 =
            let uu____6869 =
              let uu____6874 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____6874) in
            let uu____6879 =
              let uu____6885 =
                let uu____6890 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____6890) in
              let uu____6895 =
                let uu____6901 =
                  let uu____6906 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____6906) in
                [uu____6901; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____6885 :: uu____6895 in
            uu____6869 :: uu____6879 in
          uu____6853 :: uu____6863 in
        uu____6837 :: uu____6847 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6943 =
            FStar_Util.find_map table
              (fun uu____6953  ->
                 match uu____6953 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____6966 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____6966
                     else FStar_Pervasives_Native.None) in
          (match uu____6943 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____6969 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6974 =
      let uu____6975 = FStar_Syntax_Util.un_uinst l in
      uu____6975.FStar_Syntax_Syntax.n in
    match uu____6974 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____6979 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6999)::uu____7000 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7006 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7010,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____7011))::uu____7012 -> bs
      | uu____7021 ->
          let uu____7022 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7022 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____7025 =
                 let uu____7026 = FStar_Syntax_Subst.compress t in
                 uu____7026.FStar_Syntax_Syntax.n in
               (match uu____7025 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7030) ->
                    let uu____7041 =
                      FStar_Util.prefix_until
                        (fun uu___106_7063  ->
                           match uu___106_7063 with
                           | (uu____7067,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____7068)) ->
                               false
                           | uu____7070 -> true) bs' in
                    (match uu____7041 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____7088,uu____7089) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____7126,uu____7127) ->
                         let uu____7164 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7175  ->
                                   match uu____7175 with
                                   | (x,uu____7180) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7164
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7207  ->
                                     match uu____7207 with
                                     | (x,i) ->
                                         let uu____7218 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7218, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7224 -> bs))
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
              (let uu____7248 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7248 e.FStar_Syntax_Syntax.pos)
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
          let uu____7274 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____7274
          then e
          else
            (let uu____7276 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7276
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
        (let uu____7306 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7306
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7308 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7308))
         else ());
        (let fv =
           let uu____7311 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7311
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
         let uu____7317 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___149_7327 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_7327.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_7327.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_7327.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___149_7327.FStar_Syntax_Syntax.sigattrs)
           }), uu____7317))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7339 =
        match uu___107_7339 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7340 -> false in
      let reducibility uu___108_7344 =
        match uu___108_7344 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7345 -> false in
      let assumption uu___109_7349 =
        match uu___109_7349 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7350 -> false in
      let reification uu___110_7354 =
        match uu___110_7354 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7355 -> true
        | uu____7356 -> false in
      let inferred uu___111_7360 =
        match uu___111_7360 with
        | FStar_Syntax_Syntax.Discriminator uu____7361 -> true
        | FStar_Syntax_Syntax.Projector uu____7362 -> true
        | FStar_Syntax_Syntax.RecordType uu____7365 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7370 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7375 -> false in
      let has_eq uu___112_7379 =
        match uu___112_7379 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7380 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7426 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7430 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7433 =
        let uu____7434 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7437  ->
                  match uu___113_7437 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7438 -> false)) in
        FStar_All.pipe_right uu____7434 Prims.op_Negation in
      if uu____7433
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7450 =
            let uu____7451 =
              let uu____7454 =
                let uu____7455 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7455 msg in
              (uu____7454, r) in
            FStar_Errors.Error uu____7451 in
          raise uu____7450 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7463 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7475 =
            let uu____7476 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7476 in
          if uu____7475 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____7480),uu____7481) ->
              ((let uu____7490 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7490
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7493 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7493
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7498 ->
              let uu____7503 =
                let uu____7504 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7504 in
              if uu____7503 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7509 ->
              let uu____7513 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7513 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7516 ->
              let uu____7520 =
                let uu____7521 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7521 in
              if uu____7520 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7526 ->
              let uu____7527 =
                let uu____7528 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7528 in
              if uu____7527 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7533 ->
              let uu____7534 =
                let uu____7535 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7535 in
              if uu____7534 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7540 ->
              let uu____7547 =
                let uu____7548 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7548 in
              if uu____7547 then err'1 () else ()
          | uu____7553 -> ()))
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
                          let uu____7620 =
                            let uu____7623 =
                              let uu____7624 =
                                let uu____7629 =
                                  let uu____7630 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7630 in
                                (uu____7629, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7624 in
                            FStar_Syntax_Syntax.mk uu____7623 in
                          uu____7620 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7660  ->
                                  match uu____7660 with
                                  | (x,imp) ->
                                      let uu____7667 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7667, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____7671 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7671 in
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
                             let uu____7680 =
                               let uu____7681 =
                                 let uu____7682 =
                                   let uu____7683 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7684 =
                                     let uu____7685 =
                                       let uu____7686 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7686 in
                                     [uu____7685] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7683
                                     uu____7684 in
                                 uu____7682 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____7681 in
                             FStar_Syntax_Util.refine x uu____7680 in
                           let uu____7691 =
                             let uu___150_7692 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_7692.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_7692.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7691) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7703 =
                          FStar_List.map
                            (fun uu____7716  ->
                               match uu____7716 with
                               | (x,uu____7723) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____7703 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7750  ->
                                match uu____7750 with
                                | (x,uu____7757) ->
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
                             (let uu____7768 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____7768)
                               ||
                               (let uu____7770 =
                                  let uu____7771 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7771.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7770) in
                           let quals =
                             let uu____7774 =
                               let uu____7776 =
                                 let uu____7778 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7778
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7781 =
                                 FStar_List.filter
                                   (fun uu___114_7784  ->
                                      match uu___114_7784 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7785 -> false) iquals in
                               FStar_List.append uu____7776 uu____7781 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7774 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7798 =
                                 let uu____7799 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7799 in
                               FStar_Syntax_Syntax.mk_Total uu____7798 in
                             let uu____7800 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7800 in
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
                           (let uu____7803 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7803
                            then
                              let uu____7804 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7804
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
                                             fun uu____7839  ->
                                               match uu____7839 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7855 =
                                                       let uu____7857 =
                                                         let uu____7858 =
                                                           let uu____7863 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7863,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7858 in
                                                       pos uu____7857 in
                                                     (uu____7855, b)
                                                   else
                                                     (let uu____7866 =
                                                        let uu____7868 =
                                                          let uu____7869 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7869 in
                                                        pos uu____7868 in
                                                      (uu____7866, b)))) in
                                   let pat_true =
                                     let uu____7881 =
                                       let uu____7883 =
                                         let uu____7884 =
                                           let uu____7891 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____7891, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7884 in
                                       pos uu____7883 in
                                     (uu____7881,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____7914 =
                                       let uu____7916 =
                                         let uu____7917 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7917 in
                                       pos uu____7916 in
                                     (uu____7914,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____7927 =
                                     let uu____7930 =
                                       let uu____7931 =
                                         let uu____7946 =
                                           let uu____7948 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7949 =
                                             let uu____7951 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7951] in
                                           uu____7948 :: uu____7949 in
                                         (arg_exp, uu____7946) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7931 in
                                     FStar_Syntax_Syntax.mk uu____7930 in
                                   uu____7927 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____7962 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7962
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
                                let uu____7969 =
                                  let uu____7972 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____7972 in
                                let uu____7973 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7969;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7973
                                } in
                              let impl =
                                let uu____7977 =
                                  let uu____7978 =
                                    let uu____7982 =
                                      let uu____7984 =
                                        let uu____7985 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7985
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7984] in
                                    ((false, [lb]), uu____7982) in
                                  FStar_Syntax_Syntax.Sig_let uu____7978 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7977;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____7996 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7996
                               then
                                 let uu____7997 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7997
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
                                  fun uu____8076  ->
                                    match uu____8076 with
                                    | (x,uu____8081) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8083 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8083 with
                                         | (field_name,uu____8088) ->
                                             let t =
                                               let uu____8090 =
                                                 let uu____8091 =
                                                   let uu____8094 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8094 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8091 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8090 in
                                             let only_decl =
                                               (let uu____8098 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____8098)
                                                 ||
                                                 (let uu____8100 =
                                                    let uu____8101 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8101.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8100) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8111 =
                                                   FStar_List.filter
                                                     (fun uu___115_8114  ->
                                                        match uu___115_8114
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8115 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8111
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_8124  ->
                                                         match uu___116_8124
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8125 ->
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
                                             ((let uu____8128 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8128
                                               then
                                                 let uu____8129 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8129
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
                                                           fun uu____8159  ->
                                                             match uu____8159
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8175
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8175,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8186
                                                                    =
                                                                    let uu____8188
                                                                    =
                                                                    let uu____8189
                                                                    =
                                                                    let uu____8194
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8194,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8189 in
                                                                    pos
                                                                    uu____8188 in
                                                                    (uu____8186,
                                                                    b))
                                                                   else
                                                                    (let uu____8197
                                                                    =
                                                                    let uu____8199
                                                                    =
                                                                    let uu____8200
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8200 in
                                                                    pos
                                                                    uu____8199 in
                                                                    (uu____8197,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8210 =
                                                     let uu____8212 =
                                                       let uu____8213 =
                                                         let uu____8220 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____8220,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8213 in
                                                     pos uu____8212 in
                                                   let uu____8225 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8210,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8225) in
                                                 let body =
                                                   let uu____8235 =
                                                     let uu____8238 =
                                                       let uu____8239 =
                                                         let uu____8254 =
                                                           let uu____8256 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8256] in
                                                         (arg_exp,
                                                           uu____8254) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8239 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8238 in
                                                   uu____8235
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____8268 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8268
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
                                                   let uu____8274 =
                                                     let uu____8277 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____8277 in
                                                   let uu____8278 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8274;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8278
                                                   } in
                                                 let impl =
                                                   let uu____8282 =
                                                     let uu____8283 =
                                                       let uu____8287 =
                                                         let uu____8289 =
                                                           let uu____8290 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8290
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8289] in
                                                       ((false, [lb]),
                                                         uu____8287) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8283 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8282;
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
                                                 (let uu____8301 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8301
                                                  then
                                                    let uu____8302 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8302
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8336) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____8339 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8339 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8352 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8352 with
                    | (formals,uu____8362) ->
                        let uu____8373 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8395 =
                                   let uu____8396 =
                                     let uu____8397 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8397 in
                                   FStar_Ident.lid_equals typ_lid uu____8396 in
                                 if uu____8395
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8407,uvs',tps,typ0,uu____8411,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8428 -> failwith "Impossible"
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
                        (match uu____8373 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8470 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8470 with
                              | (indices,uu____8480) ->
                                  let refine_domain =
                                    let uu____8492 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_8496  ->
                                              match uu___117_8496 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8497 -> true
                                              | uu____8502 -> false)) in
                                    if uu____8492
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_8509 =
                                      match uu___118_8509 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8511,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8518 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____8519 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8519 with
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
                                    let uu____8527 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8527 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8565  ->
                                               fun uu____8566  ->
                                                 match (uu____8565,
                                                         uu____8566)
                                                 with
                                                 | ((x,uu____8576),(x',uu____8578))
                                                     ->
                                                     let uu____8583 =
                                                       let uu____8588 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8588) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8583) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8589 -> []