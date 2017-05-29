open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv option* FStar_Syntax_Syntax.lcomp)
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
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
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
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
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
  = fun env  -> fun k  -> let uu____59 = new_uvar_aux env k in fst uu____59
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
          (FStar_Syntax_Syntax.term* (FStar_Syntax_Syntax.uvar*
            FStar_Range.range) Prims.list* FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____103 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____103 with
          | Some (uu____116::(tm,uu____118)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  None tm.FStar_Syntax_Syntax.pos in
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
              (fun uu____246  ->
                 match uu____246 with
                 | (x,uu____250) -> FStar_Syntax_Print.uvar_to_string x)
              uu____238 in
          FStar_All.pipe_right uu____236 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____256 =
            let uu____257 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____257 in
          FStar_Errors.err r uu____256);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____266 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____266 with
    | None  ->
        let uu____271 =
          let uu____272 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____273 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____272 uu____273 in
        failwith uu____271
    | Some tk -> tk
let force_sort s =
  let uu____288 =
    let uu____291 = force_sort' s in FStar_Syntax_Syntax.mk uu____291 in
  uu____288 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____308  ->
      match uu____308 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____315;
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
                   let uu____347 =
                     let uu____348 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____348.FStar_Syntax_Syntax.n in
                   match uu____347 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____353 = FStar_Syntax_Util.type_u () in
                       (match uu____353 with
                        | (k,uu____359) ->
                            let t2 =
                              let uu____361 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____361
                                FStar_Pervasives.fst in
                            ((let uu___118_366 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_366.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_366.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____367 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____392) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____399) ->
                       ((fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____445) ->
                       let uu____468 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____492  ->
                                 fun uu____493  ->
                                   match (uu____492, uu____493) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____535 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____535 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____468 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____596 = aux must_check_ty1 scope body in
                            (match uu____596 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____613 =
                                         FStar_Options.ml_ish () in
                                       if uu____613
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____620 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____620
                                   then
                                     let uu____621 =
                                       FStar_Range.string_of_range r in
                                     let uu____622 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____623 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____621 uu____622 uu____623
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____631 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____639 =
                            let uu____642 =
                              let uu____643 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____643
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____642 in
                          (uu____639, false)) in
                 let uu____650 =
                   let uu____655 = t_binders env in aux false uu____655 e in
                 match uu____650 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____672 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____672
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____676 =
                                let uu____677 =
                                  let uu____680 =
                                    let uu____681 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____681 in
                                  (uu____680, rng) in
                                FStar_Errors.Error uu____677 in
                              raise uu____676)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____688 ->
               let uu____689 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____689 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____770) ->
              let uu____775 = FStar_Syntax_Util.type_u () in
              (match uu____775 with
               | (k,uu____788) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_791 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_791.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_791.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____792 =
                     let uu____795 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____795 t in
                   (match uu____792 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_810 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___120_810.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___120_810.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____817 = FStar_Syntax_Util.type_u () in
              (match uu____817 with
               | (t,uu____830) ->
                   let x1 =
                     let uu___121_832 = x in
                     let uu____833 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_832.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_832.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____833
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
              let uu____855 = FStar_Syntax_Util.type_u () in
              (match uu____855 with
               | (t,uu____868) ->
                   let x1 =
                     let uu___122_870 = x in
                     let uu____871 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_870.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_870.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____871
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____903 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____959  ->
                        fun uu____960  ->
                          match (uu____959, uu____960) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1059 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1059 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____903 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1167 =
                       let uu____1170 =
                         let uu____1171 =
                           let uu____1176 =
                             let uu____1179 =
                               let uu____1180 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1181 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1180
                                 uu____1181 in
                             uu____1179 None p1.FStar_Syntax_Syntax.p in
                           (uu____1176,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1171 in
                       FStar_Syntax_Syntax.mk uu____1170 in
                     uu____1167 None p1.FStar_Syntax_Syntax.p in
                   let uu____1198 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1204 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1210 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1198, uu____1204, uu____1210, env2, e,
                     (let uu___123_1223 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___123_1223.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___123_1223.FStar_Syntax_Syntax.p)
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
                  (fun uu____1285  ->
                     match uu____1285 with
                     | (p2,imp) ->
                         let uu____1300 = elaborate_pat env1 p2 in
                         (uu____1300, imp)) pats in
              let uu____1305 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1305 with
               | (uu____1314,t) ->
                   let uu____1316 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1316 with
                    | (f,uu____1327) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1402::uu____1403) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1438::uu____1439,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1479  ->
                                      match uu____1479 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1497 =
                                                   let uu____1499 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1499 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1497
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1505 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1505, true)
                                           | uu____1510 ->
                                               let uu____1512 =
                                                 let uu____1513 =
                                                   let uu____1516 =
                                                     let uu____1517 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1517 in
                                                   (uu____1516,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1513 in
                                               raise uu____1512)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1568,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1569))
                                   when p_imp ->
                                   let uu____1571 = aux formals' pats' in
                                   (p2, true) :: uu____1571
                               | (uu____1583,Some
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
                                   let uu____1594 = aux formals' pats2 in
                                   (p3, true) :: uu____1594
                               | (uu____1606,imp) ->
                                   let uu____1610 =
                                     let uu____1615 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1615) in
                                   let uu____1618 = aux formals' pats' in
                                   uu____1610 :: uu____1618) in
                        let uu___124_1628 = p1 in
                        let uu____1631 =
                          let uu____1632 =
                            let uu____1640 = aux f pats1 in (fv, uu____1640) in
                          FStar_Syntax_Syntax.Pat_cons uu____1632 in
                        {
                          FStar_Syntax_Syntax.v = uu____1631;
                          FStar_Syntax_Syntax.ty =
                            (uu___124_1628.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___124_1628.FStar_Syntax_Syntax.p)
                        }))
          | uu____1651 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1677 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1677 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1707 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1707 with
               | Some x ->
                   let uu____1720 =
                     let uu____1721 =
                       let uu____1724 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1724, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1721 in
                   raise uu____1720
               | uu____1733 -> (b, a, w, arg, p3)) in
        let uu____1738 = one_pat true env p in
        match uu____1738 with
        | (b,uu____1752,uu____1753,tm,p1) -> (b, tm, p1)
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
          | (uu____1794,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1796)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1801,FStar_Syntax_Syntax.Tm_constant uu____1802) ->
              let uu____1803 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1803
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1807 =
                    let uu____1808 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1809 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1808 uu____1809 in
                  failwith uu____1807)
               else ();
               (let uu____1812 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1812
                then
                  let uu____1813 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1814 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1813
                    uu____1814
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_1818 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_1818.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_1818.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1822 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1822
                then
                  let uu____1823 =
                    let uu____1824 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1825 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1824 uu____1825 in
                  failwith uu____1823
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1829 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1829.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1829.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1831),uu____1832) ->
              let s = force_sort e1 in
              let x1 =
                let uu___127_1841 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___127_1841.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___127_1841.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1854 =
                  let uu____1855 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1855 in
                if uu____1854
                then
                  let uu____1856 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1856
                else ());
               (let uu____1866 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1866))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1879;
                FStar_Syntax_Syntax.pos = uu____1880;
                FStar_Syntax_Syntax.vars = uu____1881;_},args))
              ->
              ((let uu____1908 =
                  let uu____1909 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1909 Prims.op_Negation in
                if uu____1908
                then
                  let uu____1910 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1910
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____1998 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____1998
                  | (arg::args2,(argpat,uu____2011)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2061) ->
                           let x =
                             let uu____2077 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2077 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2091) ->
                           let pat =
                             let uu____2106 = aux argpat e2 in
                             let uu____2107 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2106, uu____2107) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2110 ->
                      let uu____2124 =
                        let uu____2125 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2126 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2125 uu____2126 in
                      failwith uu____2124 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2136;
                     FStar_Syntax_Syntax.pos = uu____2137;
                     FStar_Syntax_Syntax.vars = uu____2138;_},uu____2139);
                FStar_Syntax_Syntax.tk = uu____2140;
                FStar_Syntax_Syntax.pos = uu____2141;
                FStar_Syntax_Syntax.vars = uu____2142;_},args))
              ->
              ((let uu____2173 =
                  let uu____2174 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2174 Prims.op_Negation in
                if uu____2173
                then
                  let uu____2175 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2175
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2263 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2263
                  | (arg::args2,(argpat,uu____2276)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2326) ->
                           let x =
                             let uu____2342 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2342 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2356) ->
                           let pat =
                             let uu____2371 = aux argpat e2 in
                             let uu____2372 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2371, uu____2372) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2375 ->
                      let uu____2389 =
                        let uu____2390 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2391 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2390 uu____2391 in
                      failwith uu____2389 in
                match_args [] args argpats))
          | uu____2398 ->
              let uu____2401 =
                let uu____2402 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2403 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2404 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2402 uu____2403 uu____2404 in
              failwith uu____2401 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2438 =
      match uu____2438 with
      | (p,i) ->
          let uu____2448 = decorated_pattern_as_term p in
          (match uu____2448 with
           | (vars,te) ->
               let uu____2461 =
                 let uu____2464 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2464) in
               (vars, uu____2461)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2472 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2472)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2475 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2475)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2478 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2478)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2492 =
          let uu____2500 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2500 FStar_List.unzip in
        (match uu____2492 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2558 =
               let uu____2559 =
                 let uu____2560 =
                   let uu____2570 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2570, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2560 in
               mk1 uu____2559 in
             (vars1, uu____2558))
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
      | (wp,uu____2599)::[] -> wp
      | uu____2612 ->
          let uu____2618 =
            let uu____2619 =
              let uu____2620 =
                FStar_List.map
                  (fun uu____2624  ->
                     match uu____2624 with
                     | (x,uu____2628) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2620 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2619 in
          failwith uu____2618 in
    let uu____2632 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2632, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2646 = destruct_comp c in
        match uu____2646 with
        | (u,uu____2651,wp) ->
            let uu____2653 =
              let uu____2659 =
                let uu____2660 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2660 in
              [uu____2659] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2653;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2670 =
          let uu____2674 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2675 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2674 uu____2675 in
        match uu____2670 with | (m,uu____2677,uu____2678) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2688 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2688
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
        let uu____2713 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2713 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2735 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2735 with
             | (a,kwp) ->
                 let uu____2752 = destruct_comp m1 in
                 let uu____2756 = destruct_comp m2 in
                 ((md, a, kwp), uu____2752, uu____2756))
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
            let uu____2804 =
              let uu____2805 =
                let uu____2811 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2811] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2805;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2804
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
      let uu___128_2847 = lc in
      let uu____2848 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___128_2847.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2848;
        FStar_Syntax_Syntax.cflags =
          (uu___128_2847.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2851  ->
             let uu____2852 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2852)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2856 =
      let uu____2857 = FStar_Syntax_Subst.compress t in
      uu____2857.FStar_Syntax_Syntax.n in
    match uu____2856 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2860 -> true
    | uu____2868 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2880 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2880
        then c
        else
          (let uu____2882 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2882
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2912 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2912] in
                       let us =
                         let uu____2915 =
                           let uu____2917 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2917] in
                         u_res :: uu____2915 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2928 =
                         let uu____2929 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2930 =
                           let uu____2931 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2932 =
                             let uu____2934 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2935 =
                               let uu____2937 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2937] in
                             uu____2934 :: uu____2935 in
                           uu____2931 :: uu____2932 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2929 uu____2930 in
                       uu____2928 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2943 = destruct_comp c1 in
              match uu____2943 with
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
        let close1 uu____2966 =
          let uu____2967 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2967 in
        let uu___129_2968 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_2968.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_2968.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___129_2968.FStar_Syntax_Syntax.cflags);
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
          let uu____2979 =
            let uu____2980 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2980 in
          if uu____2979
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2985 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2985
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2987 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2987 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2993 =
                        let uu____2994 =
                          let uu____2995 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2996 =
                            let uu____2997 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2998 =
                              let uu____3000 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3000] in
                            uu____2997 :: uu____2998 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2995 uu____2996 in
                        uu____2994 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2993) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3006 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3006
         then
           let uu____3007 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3008 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3009 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3007
             uu____3008 uu____3009
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
          fun uu____3026  ->
            match uu____3026 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3036 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3036
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3039 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3041 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3042 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3039 uu____3041 bstr uu____3042
                  else ());
                 (let bind_it uu____3047 =
                    let uu____3048 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3048
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3058 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3058
                        then
                          let uu____3059 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3061 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3062 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3063 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3064 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3059 uu____3061 uu____3062 uu____3063
                            uu____3064
                        else ());
                       (let try_simplify uu____3075 =
                          let aux uu____3085 =
                            let uu____3086 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3086
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3105 ->
                                  let uu____3106 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3106
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3125 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3125
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3161 =
                                  let uu____3164 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3164, reason) in
                                FStar_Util.Inl uu____3161
                            | uu____3167 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3182 =
                              let uu____3183 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3183.FStar_Syntax_Syntax.n in
                            match uu____3182 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3187) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3193 -> c in
                          let uu____3194 =
                            let uu____3195 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3195 in
                          if uu____3194
                          then
                            let uu____3203 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3203
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3217 =
                                  let uu____3218 =
                                    let uu____3221 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3221) in
                                  FStar_Errors.Error uu____3218 in
                                raise uu____3217))
                          else
                            (let uu____3229 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3229
                             then subst_c2 "both total"
                             else
                               (let uu____3237 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3237
                                then
                                  let uu____3244 =
                                    let uu____3247 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3247, "both gtot") in
                                  FStar_Util.Inl uu____3244
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3263 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3264 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3264) in
                                       if uu____3263
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___130_3273 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___130_3273.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___130_3273.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3274 =
                                           let uu____3277 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3277, "c1 Tot") in
                                         FStar_Util.Inl uu____3274
                                       else aux ()
                                   | uu____3281 -> aux ()))) in
                        let uu____3286 = try_simplify () in
                        match uu____3286 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3304 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3304
                              then
                                let uu____3305 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3306 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3307 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3305 uu____3306 uu____3307
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3314 = lift_and_destruct env c1 c2 in
                            (match uu____3314 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3348 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3348]
                                   | Some x ->
                                       let uu____3350 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3350] in
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
                                   let uu____3373 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3374 =
                                     let uu____3376 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3377 =
                                       let uu____3379 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3380 =
                                         let uu____3382 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3383 =
                                           let uu____3385 =
                                             let uu____3386 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3386 in
                                           [uu____3385] in
                                         uu____3382 :: uu____3383 in
                                       uu____3379 :: uu____3380 in
                                     uu____3376 :: uu____3377 in
                                   uu____3373 :: uu____3374 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3391 =
                                     let uu____3392 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3392
                                       wp_args in
                                   uu____3391 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3436 =
                let uu____3437 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3437 in
              if uu____3436
              then f
              else (let uu____3439 = reason1 () in label uu____3439 r f)
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
            let uu___131_3450 = g in
            let uu____3451 =
              let uu____3452 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3452 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3451;
              FStar_TypeChecker_Env.deferred =
                (uu___131_3450.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_3450.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_3450.FStar_TypeChecker_Env.implicits)
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
      | uu____3464 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3481 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3485 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3485
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3492 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3492
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3497 = destruct_comp c1 in
                    match uu____3497 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3510 =
                            let uu____3511 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3512 =
                              let uu____3513 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3514 =
                                let uu____3516 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3517 =
                                  let uu____3519 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3519] in
                                uu____3516 :: uu____3517 in
                              uu____3513 :: uu____3514 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3511
                              uu____3512 in
                          uu____3510 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___132_3524 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_3524.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_3524.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_3524.FStar_Syntax_Syntax.cflags);
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
            let uu____3551 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3551
            then (lc, g0)
            else
              ((let uu____3556 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3556
                then
                  let uu____3557 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3558 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3557 uu____3558
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3564  ->
                          match uu___98_3564 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3566 -> [])) in
                let strengthen uu____3572 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3580 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3580 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3587 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3588 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3588) in
                           if uu____3587
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3595 =
                                 let uu____3596 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3596 in
                               FStar_Syntax_Util.comp_set_flags uu____3595
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3601 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3601
                           then
                             let uu____3602 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3603 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3602 uu____3603
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3606 = destruct_comp c2 in
                           match uu____3606 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3619 =
                                   let uu____3620 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3621 =
                                     let uu____3622 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3623 =
                                       let uu____3625 =
                                         let uu____3626 =
                                           let uu____3627 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3627 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3626 in
                                       let uu____3628 =
                                         let uu____3630 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3630] in
                                       uu____3625 :: uu____3628 in
                                     uu____3622 :: uu____3623 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3620
                                     uu____3621 in
                                 uu____3619 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3636 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3636
                                 then
                                   let uu____3637 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3637
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3640 =
                  let uu___133_3641 = lc in
                  let uu____3642 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3643 =
                    let uu____3645 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3646 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3646) in
                    if uu____3645 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3642;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___133_3641.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3643;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3640,
                  (let uu___134_3649 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___134_3649.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___134_3649.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___134_3649.FStar_TypeChecker_Env.implicits)
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
        let uu____3664 =
          let uu____3667 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3668 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3667, uu____3668) in
        match uu____3664 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3677 =
                let uu____3678 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3679 =
                  let uu____3680 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3681 =
                    let uu____3683 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3683] in
                  uu____3680 :: uu____3681 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3678 uu____3679 in
              uu____3677 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3691 =
                let uu____3692 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3693 =
                  let uu____3694 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3695 =
                    let uu____3697 =
                      let uu____3698 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3698 in
                    let uu____3699 =
                      let uu____3701 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3701] in
                    uu____3697 :: uu____3699 in
                  uu____3694 :: uu____3695 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3692 uu____3693 in
              uu____3691 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3709 =
                let uu____3710 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3711 =
                  let uu____3712 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3713 =
                    let uu____3715 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3716 =
                      let uu____3718 =
                        let uu____3719 =
                          let uu____3720 =
                            let uu____3721 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3721] in
                          FStar_Syntax_Util.abs uu____3720 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3719 in
                      [uu____3718] in
                    uu____3715 :: uu____3716 in
                  uu____3712 :: uu____3713 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3710 uu____3711 in
              uu____3709 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3737 = FStar_TypeChecker_Env.get_range env in
              bind uu____3737 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3755 =
            let uu____3756 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3756
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3759 =
                 let uu____3772 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3773 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3772 uu____3773 in
               match uu____3759 with
               | ((md,uu____3775,uu____3776),(u_res_t,res_t,wp_then),
                  (uu____3780,uu____3781,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3810 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3811 =
                       let uu____3812 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3813 =
                         let uu____3814 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3815 =
                           let uu____3817 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3818 =
                             let uu____3820 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3821 =
                               let uu____3823 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3823] in
                             uu____3820 :: uu____3821 in
                           uu____3817 :: uu____3818 in
                         uu____3814 :: uu____3815 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3812 uu____3813 in
                     uu____3811 None uu____3810 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3831 =
                     let uu____3832 = FStar_Options.split_cases () in
                     uu____3832 > (Prims.parse_int "0") in
                   if uu____3831
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3838 =
                          let uu____3839 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3840 =
                            let uu____3841 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3842 =
                              let uu____3844 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3844] in
                            uu____3841 :: uu____3842 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3839 uu____3840 in
                        uu____3838 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3849 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3849;
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
      let uu____3856 =
        let uu____3857 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3857 in
      FStar_Syntax_Syntax.fvar uu____3856 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3877  ->
                 match uu____3877 with
                 | (uu____3880,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3885 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3887 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3887
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3907 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3908 =
                 let uu____3909 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3910 =
                   let uu____3911 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3912 =
                     let uu____3914 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3915 =
                       let uu____3917 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3918 =
                         let uu____3920 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3920] in
                       uu____3917 :: uu____3918 in
                     uu____3914 :: uu____3915 in
                   uu____3911 :: uu____3912 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3909 uu____3910 in
               uu____3908 None uu____3907 in
             let default_case =
               let post_k =
                 let uu____3929 =
                   let uu____3933 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3933] in
                 let uu____3934 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3929 uu____3934 in
               let kwp =
                 let uu____3940 =
                   let uu____3944 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3944] in
                 let uu____3945 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3940 uu____3945 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3950 =
                   let uu____3951 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3951] in
                 let uu____3952 =
                   let uu____3953 =
                     let uu____3956 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3956 in
                   let uu____3957 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3953 uu____3957 in
                 FStar_Syntax_Util.abs uu____3950 uu____3952
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
                 (fun uu____3971  ->
                    fun celse  ->
                      match uu____3971 with
                      | (g,cthen) ->
                          let uu____3977 =
                            let uu____3990 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3990 celse in
                          (match uu____3977 with
                           | ((md,uu____3992,uu____3993),(uu____3994,uu____3995,wp_then),
                              (uu____3997,uu____3998,wp_else)) ->
                               let uu____4009 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4009 []))
                 lcases default_case in
             let uu____4010 =
               let uu____4011 = FStar_Options.split_cases () in
               uu____4011 > (Prims.parse_int "0") in
             if uu____4010
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4015 = destruct_comp comp1 in
                match uu____4015 with
                | (uu____4019,uu____4020,wp) ->
                    let wp1 =
                      let uu____4025 =
                        let uu____4026 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4027 =
                          let uu____4028 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4029 =
                            let uu____4031 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4031] in
                          uu____4028 :: uu____4029 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4026 uu____4027 in
                      uu____4025 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4047 =
            ((let uu____4048 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4048) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4049 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4049) in
          if uu____4047
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4057 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4061 =
            (let uu____4062 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4062) || env.FStar_TypeChecker_Env.lax in
          if uu____4061
          then c
          else
            (let uu____4066 = FStar_Syntax_Util.is_partial_return c in
             if uu____4066
             then c
             else
               (let uu____4070 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4070
                then
                  let uu____4073 =
                    let uu____4074 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4074 in
                  (if uu____4073
                   then
                     let uu____4077 =
                       let uu____4078 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4079 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4078 uu____4079 in
                     failwith uu____4077
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4084 =
                        let uu____4085 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4085 in
                      if uu____4084
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___135_4090 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___135_4090.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___135_4090.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___135_4090.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4101 =
                       let uu____4104 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4104
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4101 in
                   let eq1 =
                     let uu____4108 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4108 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4110 =
                     let uu____4111 =
                       let uu____4116 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4116.FStar_Syntax_Syntax.comp in
                     uu____4111 () in
                   FStar_Syntax_Util.comp_set_flags uu____4110 flags))) in
        let uu___136_4118 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_4118.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_4118.FStar_Syntax_Syntax.res_typ);
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
          let uu____4137 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4137 with
          | None  ->
              let uu____4142 =
                let uu____4143 =
                  let uu____4146 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4147 = FStar_TypeChecker_Env.get_range env in
                  (uu____4146, uu____4147) in
                FStar_Errors.Error uu____4143 in
              raise uu____4142
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
            let uu____4173 =
              let uu____4174 = FStar_Syntax_Subst.compress t2 in
              uu____4174.FStar_Syntax_Syntax.n in
            match uu____4173 with
            | FStar_Syntax_Syntax.Tm_type uu____4177 -> true
            | uu____4178 -> false in
          let uu____4179 =
            let uu____4180 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4180.FStar_Syntax_Syntax.n in
          match uu____4179 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4186 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4193 =
                  let uu____4194 =
                    let uu____4195 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4195 in
                  (None, uu____4194) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4193 in
              let e1 =
                let uu____4204 =
                  let uu____4205 =
                    let uu____4206 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4206] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4205 in
                uu____4204
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4213 -> (e, lc)
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
              (let uu____4233 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4233 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4246 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4258 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4258, false)
            else
              (let uu____4262 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4262, true)) in
          match gopt with
          | (None ,uu____4268) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___137_4271 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___137_4271.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___137_4271.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___137_4271.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4275 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4275 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___138_4280 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___138_4280.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___138_4280.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___138_4280.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4283 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4283.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4283.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4283.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4289 =
                     let uu____4290 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4290
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4295 =
                          let uu____4296 = FStar_Syntax_Subst.compress f1 in
                          uu____4296.FStar_Syntax_Syntax.n in
                        match uu____4295 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4301,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4303;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4304;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4305;_},uu____4306)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4330 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___140_4330.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___140_4330.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___140_4330.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4331 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4336 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4336
                              then
                                let uu____4337 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4338 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4339 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4340 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4337 uu____4338 uu____4339 uu____4340
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4343 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4343 with
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
                                  let uu____4354 = destruct_comp ct in
                                  (match uu____4354 with
                                   | (u_t,uu____4361,uu____4362) ->
                                       let wp =
                                         let uu____4366 =
                                           let uu____4367 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4368 =
                                             let uu____4369 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4370 =
                                               let uu____4372 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4372] in
                                             uu____4369 :: uu____4370 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4367 uu____4368 in
                                         uu____4366
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4378 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4378 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4388 =
                                             let uu____4389 =
                                               let uu____4390 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4390] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4389 in
                                           uu____4388
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4396 =
                                         let uu____4399 =
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4410 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4411 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4399
                                           uu____4410 e cret uu____4411 in
                                       (match uu____4396 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___141_4417 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___141_4417.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___141_4417.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4419 =
                                                let uu____4420 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4420 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4419
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4430 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4430
                                              then
                                                let uu____4431 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4431
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4437  ->
                             match uu___99_4437 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4439 -> [])) in
                   let lc1 =
                     let uu___142_4441 = lc in
                     let uu____4442 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4442;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___143_4444 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4444.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4444.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4444.FStar_TypeChecker_Env.implicits)
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
        let uu____4464 =
          let uu____4465 =
            let uu____4466 =
              let uu____4467 =
                let uu____4468 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4468 in
              [uu____4467] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4466 in
          uu____4465 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4464 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4477 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4477
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4488 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4497 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4514)::(ens,uu____4516)::uu____4517 ->
                    let uu____4539 =
                      let uu____4541 = norm req in Some uu____4541 in
                    let uu____4542 =
                      let uu____4543 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4543 in
                    (uu____4539, uu____4542)
                | uu____4545 ->
                    let uu____4551 =
                      let uu____4552 =
                        let uu____4555 =
                          let uu____4556 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4556 in
                        (uu____4555, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4552 in
                    raise uu____4551)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4566)::uu____4567 ->
                    let uu____4581 =
                      let uu____4584 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4584 in
                    (match uu____4581 with
                     | (us_r,uu____4601) ->
                         let uu____4602 =
                           let uu____4605 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4605 in
                         (match uu____4602 with
                          | (us_e,uu____4622) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4625 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4625
                                  us_r in
                              let as_ens =
                                let uu____4627 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4627
                                  us_e in
                              let req =
                                let uu____4631 =
                                  let uu____4632 =
                                    let uu____4633 =
                                      let uu____4640 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4640] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4633 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4632 in
                                uu____4631
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4656 =
                                  let uu____4657 =
                                    let uu____4658 =
                                      let uu____4665 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4665] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4658 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4657 in
                                uu____4656 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4678 =
                                let uu____4680 = norm req in Some uu____4680 in
                              let uu____4681 =
                                let uu____4682 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4682 in
                              (uu____4678, uu____4681)))
                | uu____4684 -> failwith "Impossible"))
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
      (let uu____4704 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4704
       then
         let uu____4705 = FStar_Syntax_Print.term_to_string tm in
         let uu____4706 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4705 uu____4706
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
        (let uu____4727 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4727
         then
           let uu____4728 = FStar_Syntax_Print.term_to_string tm in
           let uu____4729 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4728
             uu____4729
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4734 =
      let uu____4735 =
        let uu____4736 = FStar_Syntax_Subst.compress t in
        uu____4736.FStar_Syntax_Syntax.n in
      match uu____4735 with
      | FStar_Syntax_Syntax.Tm_app uu____4739 -> false
      | uu____4749 -> true in
    if uu____4734
    then t
    else
      (let uu____4751 = FStar_Syntax_Util.head_and_args t in
       match uu____4751 with
       | (head1,args) ->
           let uu____4777 =
             let uu____4778 =
               let uu____4779 = FStar_Syntax_Subst.compress head1 in
               uu____4779.FStar_Syntax_Syntax.n in
             match uu____4778 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4782 -> false in
           if uu____4777
           then
             (match args with
              | x::[] -> fst x
              | uu____4798 ->
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
             let uu____4826 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4826 with
             | (formals,uu____4835) ->
                 let n_implicits =
                   let uu____4847 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4884  ->
                             match uu____4884 with
                             | (uu____4888,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4847 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4960 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4960 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4974 =
                     let uu____4975 =
                       let uu____4978 =
                         let uu____4979 = FStar_Util.string_of_int n_expected in
                         let uu____4983 = FStar_Syntax_Print.term_to_string e in
                         let uu____4984 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4979 uu____4983 uu____4984 in
                       let uu____4988 = FStar_TypeChecker_Env.get_range env in
                       (uu____4978, uu____4988) in
                     FStar_Errors.Error uu____4975 in
                   raise uu____4974
                 else Some (n_available - n_expected) in
           let decr_inst uu___100_5001 =
             match uu___100_5001 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5020 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5020 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_30,uu____5081) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5103,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5122 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5122 with
                           | (v1,uu____5143,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5153 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5153 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5202 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5202)))
                      | (uu____5216,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5240 =
                      let uu____5254 = inst_n_binders t in
                      aux [] uu____5254 bs1 in
                    (match uu____5240 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5292) -> (e, torig, guard)
                          | (uu____5308,[]) when
                              let uu____5324 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5324 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5325 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5344 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5359 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5365 =
      let uu____5367 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5367
        (FStar_List.map
           (fun u  ->
              let uu____5372 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5372 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5365 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5384 = FStar_Util.set_is_empty x in
      if uu____5384
      then []
      else
        (let s =
           let uu____5389 =
             let uu____5391 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5391 in
           FStar_All.pipe_right uu____5389 FStar_Util.set_elements in
         (let uu____5396 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5396
          then
            let uu____5397 =
              let uu____5398 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5398 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5397
          else ());
         (let r =
            let uu____5403 = FStar_TypeChecker_Env.get_range env in
            Some uu____5403 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5411 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5411
                     then
                       let uu____5412 =
                         let uu____5413 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5413 in
                       let uu____5414 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5415 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5412 uu____5414 uu____5415
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
        let uu____5432 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5432 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5459 =
  match uu___101_5459 with
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
        | ([],uu____5500) -> generalized_univ_names
        | (uu____5504,[]) -> explicit_univ_names
        | uu____5508 ->
            let uu____5513 =
              let uu____5514 =
                let uu____5517 =
                  let uu____5518 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5518 in
                (uu____5517, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5514 in
            raise uu____5513
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
      (let uu____5532 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5532
       then
         let uu____5533 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5533
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5538 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5538
        then
          let uu____5539 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5539
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5544 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5544))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5574 =
        let uu____5575 =
          FStar_Util.for_all
            (fun uu____5580  ->
               match uu____5580 with
               | (uu____5585,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5575 in
      if uu____5574
      then None
      else
        (let norm c =
           (let uu____5608 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5608
            then
              let uu____5609 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5609
            else ());
           (let c1 =
              let uu____5612 = FStar_TypeChecker_Env.should_verify env in
              if uu____5612
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5615 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5615
             then
               let uu____5616 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5616
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5650 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5650 FStar_Util.set_elements in
         let uu____5694 =
           let uu____5712 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5767  ->
                     match uu____5767 with
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
           FStar_All.pipe_right uu____5712 FStar_List.unzip in
         match uu____5694 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5924 = FStar_Syntax_Free.new_universe_uvar_set () in
               FStar_List.fold_left FStar_Util.set_union uu____5924 univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5931 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5931
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
                      (fun uu____5969  ->
                         match uu____5969 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6006  ->
                                       match uu____6006 with
                                       | (u,k) ->
                                           let uu____6014 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6014 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6020;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6021;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6022;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6028,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6030;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6031;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6032;_},uu____6033);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6034;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6035;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6036;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6064 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6068 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6071 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6071 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6095 =
                                                         let uu____6097 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              Some _0_31)
                                                           uu____6097 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6095 kres in
                                                     let t =
                                                       let uu____6100 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6101 =
                                                         let uu____6108 =
                                                           let uu____6114 =
                                                             let uu____6115 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6115 in
                                                           FStar_Util.Inl
                                                             uu____6114 in
                                                         Some uu____6108 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6100
                                                         uu____6101 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6128 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6146 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6146, c)
                               | ([],uu____6147) ->
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
                               | uu____6159 ->
                                   let uu____6167 = (e, c) in
                                   (match uu____6167 with
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
                                          let uu____6179 =
                                            let uu____6180 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6180.FStar_Syntax_Syntax.n in
                                          match uu____6179 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6197 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6197 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6207 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6217 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6217)) in
                             (match uu____6128 with
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
      (let uu____6255 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6255
       then
         let uu____6256 =
           let uu____6257 =
             FStar_List.map
               (fun uu____6262  ->
                  match uu____6262 with
                  | (lb,uu____6267,uu____6268) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6257 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6256
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6278  ->
              match uu____6278 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6293 =
           let uu____6300 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6316  ->
                     match uu____6316 with | (uu____6322,e,c) -> (e, c))) in
           gen env uu____6300 in
         match uu____6293 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6354  ->
                     match uu____6354 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6398  ->
                  fun uu____6399  ->
                    match (uu____6398, uu____6399) with
                    | ((l,uu____6432,uu____6433),(us,e,c)) ->
                        ((let uu____6459 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6459
                          then
                            let uu____6460 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6461 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6462 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6463 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6460 uu____6461 uu____6462 uu____6463
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6482  ->
              match uu____6482 with
              | (l,generalized_univs,t,c) ->
                  let uu____6500 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6500, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6533 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6533 with
               | None  -> None
               | Some f ->
                   let uu____6537 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____6537) in
          let is_var e1 =
            let uu____6543 =
              let uu____6544 = FStar_Syntax_Subst.compress e1 in
              uu____6544.FStar_Syntax_Syntax.n in
            match uu____6543 with
            | FStar_Syntax_Syntax.Tm_name uu____6547 -> true
            | uu____6548 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___144_6566 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_6566.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_6566.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6567 ->
                let uu___145_6568 = e2 in
                let uu____6569 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6568.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6569;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6568.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6568.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___146_6578 = env1 in
            let uu____6579 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6578.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6578.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6578.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6578.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6578.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6578.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6578.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6578.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6578.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6578.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6578.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6578.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6578.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6578.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6578.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6579;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6578.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6578.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6578.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6578.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6578.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6578.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6578.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6578.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6580 = check env2 t1 t2 in
          match uu____6580 with
          | None  ->
              let uu____6584 =
                let uu____6585 =
                  let uu____6588 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6589 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6588, uu____6589) in
                FStar_Errors.Error uu____6585 in
              raise uu____6584
          | Some g ->
              ((let uu____6594 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6594
                then
                  let uu____6595 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6595
                else ());
               (let uu____6597 = decorate e t2 in (uu____6597, g)))
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
        let uu____6621 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6621
        then
          let uu____6624 = discharge g1 in
          let uu____6625 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6624, uu____6625)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6637 =
               let uu____6638 =
                 let uu____6639 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6639 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6638
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6637
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6641 = destruct_comp c1 in
           match uu____6641 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6653 = FStar_TypeChecker_Env.get_range env in
                 let uu____6654 =
                   let uu____6655 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6656 =
                     let uu____6657 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6658 =
                       let uu____6660 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6660] in
                     uu____6657 :: uu____6658 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6655 uu____6656 in
                 uu____6654
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6653 in
               ((let uu____6666 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6666
                 then
                   let uu____6667 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6667
                 else ());
                (let g2 =
                   let uu____6670 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6670 in
                 let uu____6671 = discharge g2 in
                 let uu____6672 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6671, uu____6672))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6696 =
        match uu___102_6696 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6702)::[] -> f fst1
        | uu____6715 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6720 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6720
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____6729 =
          let uu____6732 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6732 in
        FStar_All.pipe_right uu____6729
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____6743 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6743
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_6757 =
        match uu___103_6757 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6763)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6778)::[] ->
            let uu____6799 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6799
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____6804 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6811 =
          let uu____6816 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6816) in
        let uu____6821 =
          let uu____6827 =
            let uu____6832 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6832) in
          let uu____6837 =
            let uu____6843 =
              let uu____6848 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6848) in
            let uu____6853 =
              let uu____6859 =
                let uu____6864 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6864) in
              let uu____6869 =
                let uu____6875 =
                  let uu____6880 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6880) in
                [uu____6875; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6859 :: uu____6869 in
            uu____6843 :: uu____6853 in
          uu____6827 :: uu____6837 in
        uu____6811 :: uu____6821 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6921 =
            FStar_Util.find_map table
              (fun uu____6927  ->
                 match uu____6927 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6940 = mk1 seen_args in Some uu____6940
                     else None) in
          (match uu____6921 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6943 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6947 =
      let uu____6948 = FStar_Syntax_Util.un_uinst l in
      uu____6948.FStar_Syntax_Syntax.n in
    match uu____6947 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6952 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6970)::uu____6971 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6977 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6981,Some (FStar_Syntax_Syntax.Implicit uu____6982))::uu____6983
          -> bs
      | uu____6992 ->
          let uu____6993 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6993 with
           | None  -> bs
           | Some t ->
               let uu____6996 =
                 let uu____6997 = FStar_Syntax_Subst.compress t in
                 uu____6997.FStar_Syntax_Syntax.n in
               (match uu____6996 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7001) ->
                    let uu____7012 =
                      FStar_Util.prefix_until
                        (fun uu___104_7031  ->
                           match uu___104_7031 with
                           | (uu____7035,Some (FStar_Syntax_Syntax.Implicit
                              uu____7036)) -> false
                           | uu____7038 -> true) bs' in
                    (match uu____7012 with
                     | None  -> bs
                     | Some ([],uu____7056,uu____7057) -> bs
                     | Some (imps,uu____7094,uu____7095) ->
                         let uu____7132 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7140  ->
                                   match uu____7140 with
                                   | (x,uu____7145) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7132
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7168  ->
                                     match uu____7168 with
                                     | (x,i) ->
                                         let uu____7179 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7179, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7185 -> bs))
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
              (let uu____7204 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7204 e.FStar_Syntax_Syntax.pos)
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
          let uu____7226 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7226
          then e
          else
            (let uu____7228 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7228
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
        (let uu____7254 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7254
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7256 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7256))
         else ());
        (let fv =
           let uu____7259 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7259 None in
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
         let uu____7266 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___147_7275 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_7275.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_7275.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_7275.FStar_Syntax_Syntax.sigmeta)
           }), uu____7266))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7285 =
        match uu___105_7285 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7286 -> false in
      let reducibility uu___106_7290 =
        match uu___106_7290 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7291 -> false in
      let assumption uu___107_7295 =
        match uu___107_7295 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7296 -> false in
      let reification uu___108_7300 =
        match uu___108_7300 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7301 -> true
        | uu____7302 -> false in
      let inferred uu___109_7306 =
        match uu___109_7306 with
        | FStar_Syntax_Syntax.Discriminator uu____7307 -> true
        | FStar_Syntax_Syntax.Projector uu____7308 -> true
        | FStar_Syntax_Syntax.RecordType uu____7311 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7316 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7321 -> false in
      let has_eq uu___110_7325 =
        match uu___110_7325 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7326 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7360 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7363 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7366 =
        let uu____7367 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7369  ->
                  match uu___111_7369 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7370 -> false)) in
        FStar_All.pipe_right uu____7367 Prims.op_Negation in
      if uu____7366
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7380 =
            let uu____7381 =
              let uu____7384 =
                let uu____7385 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7385 msg in
              (uu____7384, r) in
            FStar_Errors.Error uu____7381 in
          raise uu____7380 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7393 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7401 =
            let uu____7402 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7402 in
          if uu____7401 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7406),uu____7407,uu____7408) ->
              ((let uu____7419 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7419
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7422 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7422
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7426 ->
              let uu____7431 =
                let uu____7432 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7432 in
              if uu____7431 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7436 ->
              let uu____7440 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7440 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7443 ->
              let uu____7446 =
                let uu____7447 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7447 in
              if uu____7446 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7451 ->
              let uu____7452 =
                let uu____7453 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7453 in
              if uu____7452 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7457 ->
              let uu____7458 =
                let uu____7459 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7459 in
              if uu____7458 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7463 ->
              let uu____7470 =
                let uu____7471 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7471 in
              if uu____7470 then err'1 () else ()
          | uu____7475 -> ()))
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
                          let uu____7532 =
                            let uu____7535 =
                              let uu____7536 =
                                let uu____7541 =
                                  let uu____7542 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7542 in
                                (uu____7541, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7536 in
                            FStar_Syntax_Syntax.mk uu____7535 in
                          uu____7532 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7568  ->
                                  match uu____7568 with
                                  | (x,imp) ->
                                      let uu____7575 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7575, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7579 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7579 in
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
                             let uu____7588 =
                               let uu____7589 =
                                 let uu____7590 =
                                   let uu____7591 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7592 =
                                     let uu____7593 =
                                       let uu____7594 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7594 in
                                     [uu____7593] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7591
                                     uu____7592 in
                                 uu____7590 None p in
                               FStar_Syntax_Util.b2t uu____7589 in
                             FStar_Syntax_Util.refine x uu____7588 in
                           let uu____7599 =
                             let uu___148_7600 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_7600.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_7600.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7599) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7610 =
                          FStar_List.map
                            (fun uu____7620  ->
                               match uu____7620 with
                               | (x,uu____7627) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7610 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7651  ->
                                match uu____7651 with
                                | (x,uu____7658) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7667 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7667)
                               ||
                               (let uu____7668 =
                                  let uu____7669 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7669.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7668) in
                           let quals =
                             let uu____7672 =
                               let uu____7674 =
                                 let uu____7676 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7676
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7679 =
                                 FStar_List.filter
                                   (fun uu___112_7681  ->
                                      match uu___112_7681 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7682 -> false) iquals in
                               FStar_List.append uu____7674 uu____7679 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7672 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7695 =
                                 let uu____7696 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7696 in
                               FStar_Syntax_Syntax.mk_Total uu____7695 in
                             let uu____7697 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7697 in
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
                           (let uu____7700 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7700
                            then
                              let uu____7701 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7701
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
                                             fun uu____7729  ->
                                               match uu____7729 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7745 =
                                                       let uu____7748 =
                                                         let uu____7749 =
                                                           let uu____7754 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7754,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7749 in
                                                       pos uu____7748 in
                                                     (uu____7745, b)
                                                   else
                                                     (let uu____7758 =
                                                        let uu____7761 =
                                                          let uu____7762 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7762 in
                                                        pos uu____7761 in
                                                      (uu____7758, b)))) in
                                   let pat_true =
                                     let uu____7774 =
                                       let uu____7777 =
                                         let uu____7778 =
                                           let uu____7786 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7786, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7778 in
                                       pos uu____7777 in
                                     (uu____7774, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7808 =
                                       let uu____7811 =
                                         let uu____7812 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7812 in
                                       pos uu____7811 in
                                     (uu____7808, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7821 =
                                     let uu____7824 =
                                       let uu____7825 =
                                         let uu____7841 =
                                           let uu____7843 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7844 =
                                             let uu____7846 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7846] in
                                           uu____7843 :: uu____7844 in
                                         (arg_exp, uu____7841) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7825 in
                                     FStar_Syntax_Syntax.mk uu____7824 in
                                   uu____7821 None p) in
                              let dd =
                                let uu____7857 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7857
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
                                let uu____7869 =
                                  let uu____7872 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7872 in
                                let uu____7873 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7869;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7873
                                } in
                              let impl =
                                let uu____7877 =
                                  let uu____7878 =
                                    let uu____7884 =
                                      let uu____7886 =
                                        let uu____7887 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7887
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7886] in
                                    ((false, [lb]), uu____7884, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7878 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7877;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7902 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7902
                               then
                                 let uu____7903 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7903
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
                                fun uu____7923  ->
                                  match uu____7923 with
                                  | (a,uu____7927) ->
                                      let uu____7928 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7928 with
                                       | (field_name,uu____7932) ->
                                           let field_proj_tm =
                                             let uu____7934 =
                                               let uu____7935 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7935 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7934 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7949 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7958  ->
                                    match uu____7958 with
                                    | (x,uu____7963) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7965 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7965 with
                                         | (field_name,uu____7970) ->
                                             let t =
                                               let uu____7972 =
                                                 let uu____7973 =
                                                   let uu____7976 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7976 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7973 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7972 in
                                             let only_decl =
                                               ((let uu____7978 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7978)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7979 =
                                                    let uu____7980 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7980.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7979) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7990 =
                                                   FStar_List.filter
                                                     (fun uu___113_7992  ->
                                                        match uu___113_7992
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7993 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7990
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_8001  ->
                                                         match uu___114_8001
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8002 ->
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
                                             ((let uu____8005 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8005
                                               then
                                                 let uu____8006 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8006
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
                                                           fun uu____8033  ->
                                                             match uu____8033
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8049
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8049,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8061
                                                                    =
                                                                    let uu____8064
                                                                    =
                                                                    let uu____8065
                                                                    =
                                                                    let uu____8070
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8070,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8065 in
                                                                    pos
                                                                    uu____8064 in
                                                                    (uu____8061,
                                                                    b))
                                                                   else
                                                                    (let uu____8074
                                                                    =
                                                                    let uu____8077
                                                                    =
                                                                    let uu____8078
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8078 in
                                                                    pos
                                                                    uu____8077 in
                                                                    (uu____8074,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8090 =
                                                     let uu____8093 =
                                                       let uu____8094 =
                                                         let uu____8102 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8102,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8094 in
                                                     pos uu____8093 in
                                                   let uu____8108 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8090, None,
                                                     uu____8108) in
                                                 let body =
                                                   let uu____8119 =
                                                     let uu____8122 =
                                                       let uu____8123 =
                                                         let uu____8139 =
                                                           let uu____8141 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8141] in
                                                         (arg_exp,
                                                           uu____8139) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8123 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8122 in
                                                   uu____8119 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8158 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8158
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
                                                   let uu____8164 =
                                                     let uu____8167 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8167 in
                                                   let uu____8168 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8164;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8168
                                                   } in
                                                 let impl =
                                                   let uu____8172 =
                                                     let uu____8173 =
                                                       let uu____8179 =
                                                         let uu____8181 =
                                                           let uu____8182 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8182
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8181] in
                                                       ((false, [lb]),
                                                         uu____8179, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8173 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8172;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8197 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8197
                                                  then
                                                    let uu____8198 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8198
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7949 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8228) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8231 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8231 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8244 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8244 with
                    | (formals,uu____8254) ->
                        let uu____8265 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8278 =
                                   let uu____8279 =
                                     let uu____8280 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8280 in
                                   FStar_Ident.lid_equals typ_lid uu____8279 in
                                 if uu____8278
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8290,uvs',tps,typ0,uu____8294,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8307 -> failwith "Impossible"
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
                        (match uu____8265 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8349 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8349 with
                              | (indices,uu____8359) ->
                                  let refine_domain =
                                    let uu____8371 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8373  ->
                                              match uu___115_8373 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8374 -> true
                                              | uu____8379 -> false)) in
                                    if uu____8371
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8386 =
                                      match uu___116_8386 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8388,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8395 -> None in
                                    let uu____8396 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8396 with
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
                                    let uu____8404 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8404 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8435  ->
                                               fun uu____8436  ->
                                                 match (uu____8435,
                                                         uu____8436)
                                                 with
                                                 | ((x,uu____8446),(x',uu____8448))
                                                     ->
                                                     let uu____8453 =
                                                       let uu____8458 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8458) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8453) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8459 -> []