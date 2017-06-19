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
  fun uu___99_64  ->
    match uu___99_64 with
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
                     let uu___119_177 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____178 =
                       let uu____186 =
                         let uu____193 = as_uvar u in
                         (reason, env, uu____193, t, k, r) in
                       [uu____186] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_177.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_177.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_177.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___120_366 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_366.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_366.FStar_Syntax_Syntax.index);
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
                       let uu____458 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____482  ->
                                 fun uu____483  ->
                                   match (uu____482, uu____483) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____525 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____525 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____458 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____586 = aux must_check_ty1 scope body in
                            (match uu____586 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____603 =
                                         FStar_Options.ml_ish () in
                                       if uu____603
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____610 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____610
                                   then
                                     let uu____611 =
                                       FStar_Range.string_of_range r in
                                     let uu____612 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____613 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____611 uu____612 uu____613
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____621 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____629 =
                            let uu____632 =
                              let uu____633 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____633
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____632 in
                          (uu____629, false)) in
                 let uu____640 =
                   let uu____645 = t_binders env in aux false uu____645 e in
                 match uu____640 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____662 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____662
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____666 =
                                let uu____667 =
                                  let uu____670 =
                                    let uu____671 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____671 in
                                  (uu____670, rng) in
                                FStar_Errors.Error uu____667 in
                              raise uu____666)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____678 ->
               let uu____679 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____679 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____760) ->
              let uu____765 = FStar_Syntax_Util.type_u () in
              (match uu____765 with
               | (k,uu____778) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_781 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_781.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_781.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____782 =
                     let uu____785 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____785 t in
                   (match uu____782 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_800 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___122_800.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___122_800.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____807 = FStar_Syntax_Util.type_u () in
              (match uu____807 with
               | (t,uu____820) ->
                   let x1 =
                     let uu___123_822 = x in
                     let uu____823 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_822.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_822.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____823
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
              let uu____845 = FStar_Syntax_Util.type_u () in
              (match uu____845 with
               | (t,uu____858) ->
                   let x1 =
                     let uu___124_860 = x in
                     let uu____861 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_860.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_860.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____861
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____893 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____949  ->
                        fun uu____950  ->
                          match (uu____949, uu____950) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1049 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1049 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____893 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1157 =
                       let uu____1160 =
                         let uu____1161 =
                           let uu____1166 =
                             let uu____1169 =
                               let uu____1170 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1171 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1170
                                 uu____1171 in
                             uu____1169 None p1.FStar_Syntax_Syntax.p in
                           (uu____1166,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1161 in
                       FStar_Syntax_Syntax.mk uu____1160 in
                     uu____1157 None p1.FStar_Syntax_Syntax.p in
                   let uu____1188 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1194 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1200 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1188, uu____1194, uu____1200, env2, e,
                     (let uu___125_1213 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___125_1213.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___125_1213.FStar_Syntax_Syntax.p)
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
                  (fun uu____1275  ->
                     match uu____1275 with
                     | (p2,imp) ->
                         let uu____1290 = elaborate_pat env1 p2 in
                         (uu____1290, imp)) pats in
              let uu____1295 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1295 with
               | (uu____1304,t) ->
                   let uu____1306 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1306 with
                    | (f,uu____1317) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1392::uu____1393) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1428::uu____1429,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1469  ->
                                      match uu____1469 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1487 =
                                                   let uu____1489 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1489 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1487
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1495 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1495, true)
                                           | uu____1500 ->
                                               let uu____1502 =
                                                 let uu____1503 =
                                                   let uu____1506 =
                                                     let uu____1507 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1507 in
                                                   (uu____1506,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1503 in
                                               raise uu____1502)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1558,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1559))
                                   when p_imp ->
                                   let uu____1561 = aux formals' pats' in
                                   (p2, true) :: uu____1561
                               | (uu____1573,Some
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
                                   let uu____1584 = aux formals' pats2 in
                                   (p3, true) :: uu____1584
                               | (uu____1596,imp) ->
                                   let uu____1600 =
                                     let uu____1605 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1605) in
                                   let uu____1608 = aux formals' pats' in
                                   uu____1600 :: uu____1608) in
                        let uu___126_1618 = p1 in
                        let uu____1621 =
                          let uu____1622 =
                            let uu____1630 = aux f pats1 in (fv, uu____1630) in
                          FStar_Syntax_Syntax.Pat_cons uu____1622 in
                        {
                          FStar_Syntax_Syntax.v = uu____1621;
                          FStar_Syntax_Syntax.ty =
                            (uu___126_1618.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___126_1618.FStar_Syntax_Syntax.p)
                        }))
          | uu____1641 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1667 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1667 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1697 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1697 with
               | Some x ->
                   let uu____1710 =
                     let uu____1711 =
                       let uu____1714 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1714, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1711 in
                   raise uu____1710
               | uu____1723 -> (b, a, w, arg, p3)) in
        let uu____1728 = one_pat true env p in
        match uu____1728 with
        | (b,uu____1742,uu____1743,tm,p1) -> (b, tm, p1)
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
          | (uu____1784,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1786)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1791,FStar_Syntax_Syntax.Tm_constant uu____1792) ->
              let uu____1793 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1793
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1797 =
                    let uu____1798 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1799 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1798 uu____1799 in
                  failwith uu____1797)
               else ();
               (let uu____1802 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1802
                then
                  let uu____1803 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1804 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1803
                    uu____1804
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_1808 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_1808.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_1808.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1812 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1812
                then
                  let uu____1813 =
                    let uu____1814 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1815 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1814 uu____1815 in
                  failwith uu____1813
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_1819 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1819.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1819.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1821),uu____1822) ->
              let s = force_sort e1 in
              let x1 =
                let uu___129_1831 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___129_1831.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___129_1831.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1844 =
                  let uu____1845 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1845 in
                if uu____1844
                then
                  let uu____1846 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1846
                else ());
               (let uu____1856 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1856))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1869;
                FStar_Syntax_Syntax.pos = uu____1870;
                FStar_Syntax_Syntax.vars = uu____1871;_},args))
              ->
              ((let uu____1898 =
                  let uu____1899 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1899 Prims.op_Negation in
                if uu____1898
                then
                  let uu____1900 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1900
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____1988 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____1988
                  | (arg::args2,(argpat,uu____2001)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2051) ->
                           let x =
                             let uu____2067 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2067 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2081) ->
                           let pat =
                             let uu____2096 = aux argpat e2 in
                             let uu____2097 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2096, uu____2097) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2100 ->
                      let uu____2114 =
                        let uu____2115 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2116 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2115 uu____2116 in
                      failwith uu____2114 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2126;
                     FStar_Syntax_Syntax.pos = uu____2127;
                     FStar_Syntax_Syntax.vars = uu____2128;_},uu____2129);
                FStar_Syntax_Syntax.tk = uu____2130;
                FStar_Syntax_Syntax.pos = uu____2131;
                FStar_Syntax_Syntax.vars = uu____2132;_},args))
              ->
              ((let uu____2163 =
                  let uu____2164 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2164 Prims.op_Negation in
                if uu____2163
                then
                  let uu____2165 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2165
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2253 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2253
                  | (arg::args2,(argpat,uu____2266)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2316) ->
                           let x =
                             let uu____2332 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2332 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2346) ->
                           let pat =
                             let uu____2361 = aux argpat e2 in
                             let uu____2362 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2361, uu____2362) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2365 ->
                      let uu____2379 =
                        let uu____2380 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2381 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2380 uu____2381 in
                      failwith uu____2379 in
                match_args [] args argpats))
          | uu____2388 ->
              let uu____2391 =
                let uu____2392 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2393 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2394 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2392 uu____2393 uu____2394 in
              failwith uu____2391 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2428 =
      match uu____2428 with
      | (p,i) ->
          let uu____2438 = decorated_pattern_as_term p in
          (match uu____2438 with
           | (vars,te) ->
               let uu____2451 =
                 let uu____2454 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2454) in
               (vars, uu____2451)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2462 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2462)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2465 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2465)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2468 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2468)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2482 =
          let uu____2490 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2490 FStar_List.unzip in
        (match uu____2482 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2548 =
               let uu____2549 =
                 let uu____2550 =
                   let uu____2560 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2560, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2550 in
               mk1 uu____2549 in
             (vars1, uu____2548))
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
      | (wp,uu____2589)::[] -> wp
      | uu____2602 ->
          let uu____2608 =
            let uu____2609 =
              let uu____2610 =
                FStar_List.map
                  (fun uu____2614  ->
                     match uu____2614 with
                     | (x,uu____2618) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2610 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2609 in
          failwith uu____2608 in
    let uu____2622 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2622, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2636 = destruct_comp c in
        match uu____2636 with
        | (u,uu____2641,wp) ->
            let uu____2643 =
              let uu____2649 =
                let uu____2650 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2650 in
              [uu____2649] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2643;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2660 =
          let uu____2664 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2665 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2664 uu____2665 in
        match uu____2660 with | (m,uu____2667,uu____2668) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2678 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2678
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
        let uu____2703 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2703 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2725 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2725 with
             | (a,kwp) ->
                 let uu____2742 = destruct_comp m1 in
                 let uu____2746 = destruct_comp m2 in
                 ((md, a, kwp), uu____2742, uu____2746))
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
            let uu____2794 =
              let uu____2795 =
                let uu____2801 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2801] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2795;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2794
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
      let uu___130_2837 = lc in
      let uu____2838 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___130_2837.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2838;
        FStar_Syntax_Syntax.cflags =
          (uu___130_2837.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2841  ->
             let uu____2842 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2842)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2846 =
      let uu____2847 = FStar_Syntax_Subst.compress t in
      uu____2847.FStar_Syntax_Syntax.n in
    match uu____2846 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2850 -> true
    | uu____2858 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2870 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2870
        then c
        else
          (let uu____2872 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2872
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2902 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2902] in
                       let us =
                         let uu____2905 =
                           let uu____2907 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2907] in
                         u_res :: uu____2905 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Syntax_Const.effect_Tot_lid None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____2911 =
                         let uu____2912 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2913 =
                           let uu____2914 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2915 =
                             let uu____2917 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2918 =
                               let uu____2920 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2920] in
                             uu____2917 :: uu____2918 in
                           uu____2914 :: uu____2915 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2912 uu____2913 in
                       uu____2911 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2926 = destruct_comp c1 in
              match uu____2926 with
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
        let close1 uu____2949 =
          let uu____2950 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2950 in
        let uu___131_2951 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_2951.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_2951.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_2951.FStar_Syntax_Syntax.cflags);
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
          let uu____2962 =
            let uu____2963 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2963 in
          if uu____2962
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2968 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2968
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2970 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2970 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2976 =
                        let uu____2977 =
                          let uu____2978 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2979 =
                            let uu____2980 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2981 =
                              let uu____2983 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2983] in
                            uu____2980 :: uu____2981 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2978 uu____2979 in
                        uu____2977 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2976) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2989 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2989
         then
           let uu____2990 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2991 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2992 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2990
             uu____2991 uu____2992
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
          fun uu____3009  ->
            match uu____3009 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3019 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3019
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3022 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3024 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3025 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3022 uu____3024 bstr uu____3025
                  else ());
                 (let bind_it uu____3030 =
                    let uu____3031 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3031
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3041 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3041
                        then
                          let uu____3042 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3044 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3045 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3046 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3047 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3042 uu____3044 uu____3045 uu____3046
                            uu____3047
                        else ());
                       (let try_simplify uu____3058 =
                          let aux uu____3068 =
                            let uu____3069 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3069
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3088 ->
                                  let uu____3089 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3089
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3108 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3108
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3144 =
                                  let uu____3147 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3147, reason) in
                                FStar_Util.Inl uu____3144
                            | uu____3150 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3165 =
                              let uu____3166 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3166.FStar_Syntax_Syntax.n in
                            match uu____3165 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3170) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3176 -> c in
                          let uu____3177 =
                            let uu____3178 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3178 in
                          if uu____3177
                          then
                            let uu____3186 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3186
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3200 =
                                  let uu____3201 =
                                    let uu____3204 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3204) in
                                  FStar_Errors.Error uu____3201 in
                                raise uu____3200))
                          else
                            (let uu____3212 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3212
                             then subst_c2 "both total"
                             else
                               (let uu____3220 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3220
                                then
                                  let uu____3227 =
                                    let uu____3230 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3230, "both gtot") in
                                  FStar_Util.Inl uu____3227
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3246 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3247 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3247) in
                                       if uu____3246
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___132_3256 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___132_3256.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___132_3256.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3257 =
                                           let uu____3260 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3260, "c1 Tot") in
                                         FStar_Util.Inl uu____3257
                                       else aux ()
                                   | uu____3264 -> aux ()))) in
                        let uu____3269 = try_simplify () in
                        match uu____3269 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3287 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3287
                              then
                                let uu____3288 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3289 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3290 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3288 uu____3289 uu____3290
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3297 = lift_and_destruct env c1 c2 in
                            (match uu____3297 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3331 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3331]
                                   | Some x ->
                                       let uu____3333 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3333] in
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
                                   let uu____3349 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3350 =
                                     let uu____3352 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3353 =
                                       let uu____3355 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3356 =
                                         let uu____3358 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3359 =
                                           let uu____3361 =
                                             let uu____3362 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3362 in
                                           [uu____3361] in
                                         uu____3358 :: uu____3359 in
                                       uu____3355 :: uu____3356 in
                                     uu____3352 :: uu____3353 in
                                   uu____3349 :: uu____3350 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3367 =
                                     let uu____3368 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3368
                                       wp_args in
                                   uu____3367 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3412 =
                let uu____3413 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3413 in
              if uu____3412
              then f
              else (let uu____3415 = reason1 () in label uu____3415 r f)
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
            let uu___133_3426 = g in
            let uu____3427 =
              let uu____3428 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3428 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3427;
              FStar_TypeChecker_Env.deferred =
                (uu___133_3426.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_3426.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_3426.FStar_TypeChecker_Env.implicits)
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
      | uu____3438 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3455 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3459 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3459
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3466 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3466
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3471 = destruct_comp c1 in
                    match uu____3471 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3484 =
                            let uu____3485 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3486 =
                              let uu____3487 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3488 =
                                let uu____3490 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3491 =
                                  let uu____3493 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3493] in
                                uu____3490 :: uu____3491 in
                              uu____3487 :: uu____3488 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3485
                              uu____3486 in
                          uu____3484 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___134_3498 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___134_3498.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___134_3498.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___134_3498.FStar_Syntax_Syntax.cflags);
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
            let uu____3525 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3525
            then (lc, g0)
            else
              ((let uu____3530 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3530
                then
                  let uu____3531 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3532 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3531 uu____3532
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3538  ->
                          match uu___100_3538 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3540 -> [])) in
                let strengthen uu____3546 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3554 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3554 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3561 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3562 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3562) in
                           if uu____3561
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3569 =
                                 let uu____3570 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3570 in
                               FStar_Syntax_Util.comp_set_flags uu____3569
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3575 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3575
                           then
                             let uu____3576 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3577 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3576 uu____3577
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3580 = destruct_comp c2 in
                           match uu____3580 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3593 =
                                   let uu____3594 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3595 =
                                     let uu____3596 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3597 =
                                       let uu____3599 =
                                         let uu____3600 =
                                           let uu____3601 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3601 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3600 in
                                       let uu____3602 =
                                         let uu____3604 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3604] in
                                       uu____3599 :: uu____3602 in
                                     uu____3596 :: uu____3597 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3594
                                     uu____3595 in
                                 uu____3593 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3610 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3610
                                 then
                                   let uu____3611 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3611
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3614 =
                  let uu___135_3615 = lc in
                  let uu____3616 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3617 =
                    let uu____3619 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3620 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3620) in
                    if uu____3619 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3616;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___135_3615.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3617;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3614,
                  (let uu___136_3623 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___136_3623.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___136_3623.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___136_3623.FStar_TypeChecker_Env.implicits)
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
        let uu____3638 =
          let uu____3641 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3642 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3641, uu____3642) in
        match uu____3638 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3651 =
                let uu____3652 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3653 =
                  let uu____3654 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3655 =
                    let uu____3657 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3657] in
                  uu____3654 :: uu____3655 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3652 uu____3653 in
              uu____3651 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3665 =
                let uu____3666 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3667 =
                  let uu____3668 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3669 =
                    let uu____3671 =
                      let uu____3672 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3672 in
                    let uu____3673 =
                      let uu____3675 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3675] in
                    uu____3671 :: uu____3673 in
                  uu____3668 :: uu____3669 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3666 uu____3667 in
              uu____3665 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3683 =
                let uu____3684 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3685 =
                  let uu____3686 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3687 =
                    let uu____3689 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3690 =
                      let uu____3692 =
                        let uu____3693 =
                          let uu____3694 =
                            let uu____3695 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3695] in
                          FStar_Syntax_Util.abs uu____3694 x_eq_y_yret
                            (Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Syntax_Const.effect_Tot_lid None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3693 in
                      [uu____3692] in
                    uu____3689 :: uu____3690 in
                  uu____3686 :: uu____3687 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3684 uu____3685 in
              uu____3683 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3704 = FStar_TypeChecker_Env.get_range env in
              bind uu____3704 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3722 =
            let uu____3723 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3723
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3726 =
                 let uu____3739 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3740 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3739 uu____3740 in
               match uu____3726 with
               | ((md,uu____3742,uu____3743),(u_res_t,res_t,wp_then),
                  (uu____3747,uu____3748,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3777 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3778 =
                       let uu____3779 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3780 =
                         let uu____3781 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3782 =
                           let uu____3784 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3785 =
                             let uu____3787 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3788 =
                               let uu____3790 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3790] in
                             uu____3787 :: uu____3788 in
                           uu____3784 :: uu____3785 in
                         uu____3781 :: uu____3782 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3779 uu____3780 in
                     uu____3778 None uu____3777 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3798 =
                     let uu____3799 = FStar_Options.split_cases () in
                     uu____3799 > (Prims.parse_int "0") in
                   if uu____3798
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3805 =
                          let uu____3806 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3807 =
                            let uu____3808 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3809 =
                              let uu____3811 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3811] in
                            uu____3808 :: uu____3809 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3806 uu____3807 in
                        uu____3805 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3816 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3816;
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
      let uu____3823 =
        let uu____3824 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3824 in
      FStar_Syntax_Syntax.fvar uu____3823 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3844  ->
                 match uu____3844 with
                 | (uu____3847,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3852 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3854 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3854
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3874 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3875 =
                 let uu____3876 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3877 =
                   let uu____3878 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3879 =
                     let uu____3881 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3882 =
                       let uu____3884 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3885 =
                         let uu____3887 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3887] in
                       uu____3884 :: uu____3885 in
                     uu____3881 :: uu____3882 in
                   uu____3878 :: uu____3879 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3876 uu____3877 in
               uu____3875 None uu____3874 in
             let default_case =
               let post_k =
                 let uu____3896 =
                   let uu____3900 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3900] in
                 let uu____3901 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3896 uu____3901 in
               let kwp =
                 let uu____3907 =
                   let uu____3911 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3911] in
                 let uu____3912 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3907 uu____3912 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3917 =
                   let uu____3918 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3918] in
                 let uu____3919 =
                   let uu____3920 =
                     let uu____3923 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3923 in
                   let uu____3924 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3920 uu____3924 in
                 FStar_Syntax_Util.abs uu____3917 uu____3919
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
                 (fun uu____3931  ->
                    fun celse  ->
                      match uu____3931 with
                      | (g,cthen) ->
                          let uu____3937 =
                            let uu____3950 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3950 celse in
                          (match uu____3937 with
                           | ((md,uu____3952,uu____3953),(uu____3954,uu____3955,wp_then),
                              (uu____3957,uu____3958,wp_else)) ->
                               let uu____3969 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3969 []))
                 lcases default_case in
             let uu____3970 =
               let uu____3971 = FStar_Options.split_cases () in
               uu____3971 > (Prims.parse_int "0") in
             if uu____3970
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3975 = destruct_comp comp1 in
                match uu____3975 with
                | (uu____3979,uu____3980,wp) ->
                    let wp1 =
                      let uu____3985 =
                        let uu____3986 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3987 =
                          let uu____3988 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3989 =
                            let uu____3991 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3991] in
                          uu____3988 :: uu____3989 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3986 uu____3987 in
                      uu____3985 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4007 =
            ((let uu____4008 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4008) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4009 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4009) in
          if uu____4007
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4017 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4021 =
            (let uu____4022 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4022) || env.FStar_TypeChecker_Env.lax in
          if uu____4021
          then c
          else
            (let uu____4026 = FStar_Syntax_Util.is_partial_return c in
             if uu____4026
             then c
             else
               (let uu____4030 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4030
                then
                  let uu____4033 =
                    let uu____4034 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4034 in
                  (if uu____4033
                   then
                     let uu____4037 =
                       let uu____4038 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4039 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4038 uu____4039 in
                     failwith uu____4037
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4044 =
                        let uu____4045 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4045 in
                      if uu____4044
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___137_4050 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___137_4050.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___137_4050.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___137_4050.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4061 =
                       let uu____4064 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4064
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4061 in
                   let eq1 =
                     let uu____4068 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4068 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4070 =
                     let uu____4071 =
                       let uu____4076 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4076.FStar_Syntax_Syntax.comp in
                     uu____4071 () in
                   FStar_Syntax_Util.comp_set_flags uu____4070 flags))) in
        let uu___138_4078 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___138_4078.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___138_4078.FStar_Syntax_Syntax.res_typ);
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
          let uu____4097 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4097 with
          | None  ->
              let uu____4102 =
                let uu____4103 =
                  let uu____4106 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4107 = FStar_TypeChecker_Env.get_range env in
                  (uu____4106, uu____4107) in
                FStar_Errors.Error uu____4103 in
              raise uu____4102
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
            let uu____4133 =
              let uu____4134 = FStar_Syntax_Subst.compress t2 in
              uu____4134.FStar_Syntax_Syntax.n in
            match uu____4133 with
            | FStar_Syntax_Syntax.Tm_type uu____4137 -> true
            | uu____4138 -> false in
          let uu____4139 =
            let uu____4140 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4140.FStar_Syntax_Syntax.n in
          match uu____4139 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4146 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4153 =
                  let uu____4154 =
                    let uu____4155 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4155 in
                  (None, uu____4154) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4153 in
              let e1 =
                let uu____4164 =
                  let uu____4165 =
                    let uu____4166 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4166] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4165 in
                uu____4164
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4173 -> (e, lc)
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
              (let uu____4193 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4193 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4206 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4218 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4218, false)
            else
              (let uu____4222 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4222, true)) in
          match gopt with
          | (None ,uu____4228) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___139_4231 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___139_4231.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___139_4231.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___139_4231.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4235 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4235 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_4240 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_4240.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_4240.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___140_4240.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_4243 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_4243.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_4243.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_4243.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4249 =
                     let uu____4250 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4250
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4255 =
                          let uu____4256 = FStar_Syntax_Subst.compress f1 in
                          uu____4256.FStar_Syntax_Syntax.n in
                        match uu____4255 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4261,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4263;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4264;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4265;_},uu____4266)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_4280 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_4280.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_4280.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___142_4280.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4281 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4286 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4286
                              then
                                let uu____4287 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4288 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4289 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4290 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4287 uu____4288 uu____4289 uu____4290
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4293 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4293 with
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
                                  let uu____4304 = destruct_comp ct in
                                  (match uu____4304 with
                                   | (u_t,uu____4311,uu____4312) ->
                                       let wp =
                                         let uu____4316 =
                                           let uu____4317 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4318 =
                                             let uu____4319 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4320 =
                                               let uu____4322 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4322] in
                                             uu____4319 :: uu____4320 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4317 uu____4318 in
                                         uu____4316
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4328 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4328 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4338 =
                                             let uu____4339 =
                                               let uu____4340 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4340] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4339 in
                                           uu____4338
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4346 =
                                         let uu____4349 =
                                           FStar_All.pipe_left
                                             (fun _0_39  -> Some _0_39)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4360 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4361 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4349
                                           uu____4360 e cret uu____4361 in
                                       (match uu____4346 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___143_4367 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___143_4367.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___143_4367.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4369 =
                                                let uu____4370 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4370 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4369
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4380 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4380
                                              then
                                                let uu____4381 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4381
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4387  ->
                             match uu___101_4387 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4389 -> [])) in
                   let lc1 =
                     let uu___144_4391 = lc in
                     let uu____4392 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4392;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___145_4394 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___145_4394.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___145_4394.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___145_4394.FStar_TypeChecker_Env.implicits)
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
        let uu____4414 =
          let uu____4415 =
            let uu____4416 =
              let uu____4417 =
                let uu____4418 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4418 in
              [uu____4417] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4416 in
          uu____4415 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4414 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4427 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4427
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4438 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4447 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4464)::(ens,uu____4466)::uu____4467 ->
                    let uu____4489 =
                      let uu____4491 = norm req in Some uu____4491 in
                    let uu____4492 =
                      let uu____4493 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4493 in
                    (uu____4489, uu____4492)
                | uu____4495 ->
                    let uu____4501 =
                      let uu____4502 =
                        let uu____4505 =
                          let uu____4506 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4506 in
                        (uu____4505, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4502 in
                    raise uu____4501)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4516)::uu____4517 ->
                    let uu____4531 =
                      let uu____4534 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4534 in
                    (match uu____4531 with
                     | (us_r,uu____4551) ->
                         let uu____4552 =
                           let uu____4555 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4555 in
                         (match uu____4552 with
                          | (us_e,uu____4572) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4575 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4575
                                  us_r in
                              let as_ens =
                                let uu____4577 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4577
                                  us_e in
                              let req =
                                let uu____4581 =
                                  let uu____4582 =
                                    let uu____4583 =
                                      let uu____4590 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4590] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4583 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4582 in
                                uu____4581
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4606 =
                                  let uu____4607 =
                                    let uu____4608 =
                                      let uu____4615 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4615] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4608 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4607 in
                                uu____4606 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4628 =
                                let uu____4630 = norm req in Some uu____4630 in
                              let uu____4631 =
                                let uu____4632 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4632 in
                              (uu____4628, uu____4631)))
                | uu____4634 -> failwith "Impossible"))
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
      (let uu____4654 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4654
       then
         let uu____4655 = FStar_Syntax_Print.term_to_string tm in
         let uu____4656 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4655 uu____4656
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
        (let uu____4677 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4677
         then
           let uu____4678 = FStar_Syntax_Print.term_to_string tm in
           let uu____4679 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4678
             uu____4679
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4684 =
      let uu____4685 =
        let uu____4686 = FStar_Syntax_Subst.compress t in
        uu____4686.FStar_Syntax_Syntax.n in
      match uu____4685 with
      | FStar_Syntax_Syntax.Tm_app uu____4689 -> false
      | uu____4699 -> true in
    if uu____4684
    then t
    else
      (let uu____4701 = FStar_Syntax_Util.head_and_args t in
       match uu____4701 with
       | (head1,args) ->
           let uu____4727 =
             let uu____4728 =
               let uu____4729 = FStar_Syntax_Subst.compress head1 in
               uu____4729.FStar_Syntax_Syntax.n in
             match uu____4728 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4732 -> false in
           if uu____4727
           then
             (match args with
              | x::[] -> fst x
              | uu____4748 ->
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
             let uu____4776 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4776 with
             | (formals,uu____4785) ->
                 let n_implicits =
                   let uu____4797 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4834  ->
                             match uu____4834 with
                             | (uu____4838,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4797 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4910 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4910 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4924 =
                     let uu____4925 =
                       let uu____4928 =
                         let uu____4929 = FStar_Util.string_of_int n_expected in
                         let uu____4933 = FStar_Syntax_Print.term_to_string e in
                         let uu____4934 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4929 uu____4933 uu____4934 in
                       let uu____4938 = FStar_TypeChecker_Env.get_range env in
                       (uu____4928, uu____4938) in
                     FStar_Errors.Error uu____4925 in
                   raise uu____4924
                 else Some (n_available - n_expected) in
           let decr_inst uu___102_4951 =
             match uu___102_4951 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4970 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4970 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_40,uu____5031) when
                          _0_40 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5053,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5072 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5072 with
                           | (v1,uu____5093,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5103 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5103 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5152 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5152)))
                      | (uu____5166,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5190 =
                      let uu____5204 = inst_n_binders t in
                      aux [] uu____5204 bs1 in
                    (match uu____5190 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5242) -> (e, torig, guard)
                          | (uu____5258,[]) when
                              let uu____5274 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5274 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5275 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5294 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5309 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5315 =
      let uu____5317 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5317
        (FStar_List.map
           (fun u  ->
              let uu____5322 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5322 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5315 (FStar_String.concat ", ")
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
            Some uu____5353 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5361 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5361
                     then
                       let uu____5362 =
                         let uu____5363 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5363 in
                       let uu____5364 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5365 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5362 uu____5364 uu____5365
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
let maybe_set_tk ts uu___103_5409 =
  match uu___103_5409 with
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
        | ([],uu____5450) -> generalized_univ_names
        | (uu____5454,[]) -> explicit_univ_names
        | uu____5458 ->
            let uu____5463 =
              let uu____5464 =
                let uu____5467 =
                  let uu____5468 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5468 in
                (uu____5467, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5464 in
            raise uu____5463
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
      (let uu____5482 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5482
       then
         let uu____5483 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5483
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5488 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5488
        then
          let uu____5489 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5489
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5494 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5494))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5524 =
        let uu____5525 =
          FStar_Util.for_all
            (fun uu____5530  ->
               match uu____5530 with
               | (uu____5535,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5525 in
      if uu____5524
      then None
      else
        (let norm c =
           (let uu____5558 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5558
            then
              let uu____5559 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5559
            else ());
           (let c1 =
              let uu____5562 = FStar_TypeChecker_Env.should_verify env in
              if uu____5562
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5565 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5565
             then
               let uu____5566 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5566
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5600 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5600 FStar_Util.set_elements in
         let uu____5644 =
           let uu____5662 =
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
                         let uvs = gen_uvars uvt in (univs1, (uvs, e, c1)))) in
           FStar_All.pipe_right uu____5662 FStar_List.unzip in
         match uu____5644 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5874 = FStar_Syntax_Free.new_universe_uvar_set () in
               FStar_List.fold_left FStar_Util.set_union uu____5874 univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5881 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5881
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
                      (fun uu____5919  ->
                         match uu____5919 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5956  ->
                                       match uu____5956 with
                                       | (u,k) ->
                                           let uu____5964 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____5964 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____5970;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5971;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5972;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____5978,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____5980;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____5981;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____5982;_},uu____5983);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____5984;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____5985;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____5986;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6004 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6008 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6011 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6011 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6035 =
                                                         let uu____6037 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_41  ->
                                                              Some _0_41)
                                                           uu____6037 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6035 kres in
                                                     let t =
                                                       let uu____6040 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6040
                                                         (Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               kres)) in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6043 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6061 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6061, c)
                               | ([],uu____6062) ->
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
                               | uu____6074 ->
                                   let uu____6082 = (e, c) in
                                   (match uu____6082 with
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
                                          let uu____6094 =
                                            let uu____6095 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6095.FStar_Syntax_Syntax.n in
                                          match uu____6094 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6112 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6112 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6122 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____6124 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6124)) in
                             (match uu____6043 with
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
      (let uu____6162 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6162
       then
         let uu____6163 =
           let uu____6164 =
             FStar_List.map
               (fun uu____6169  ->
                  match uu____6169 with
                  | (lb,uu____6174,uu____6175) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6164 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6163
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6185  ->
              match uu____6185 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6200 =
           let uu____6207 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6223  ->
                     match uu____6223 with | (uu____6229,e,c) -> (e, c))) in
           gen env uu____6207 in
         match uu____6200 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6261  ->
                     match uu____6261 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6305  ->
                  fun uu____6306  ->
                    match (uu____6305, uu____6306) with
                    | ((l,uu____6339,uu____6340),(us,e,c)) ->
                        ((let uu____6366 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6366
                          then
                            let uu____6367 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6368 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6369 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6370 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6367 uu____6368 uu____6369 uu____6370
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6389  ->
              match uu____6389 with
              | (l,generalized_univs,t,c) ->
                  let uu____6407 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6407, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6440 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6440 with
               | None  -> None
               | Some f ->
                   let uu____6444 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_42  -> Some _0_42) uu____6444) in
          let is_var e1 =
            let uu____6450 =
              let uu____6451 = FStar_Syntax_Subst.compress e1 in
              uu____6451.FStar_Syntax_Syntax.n in
            match uu____6450 with
            | FStar_Syntax_Syntax.Tm_name uu____6454 -> true
            | uu____6455 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___146_6473 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___146_6473.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___146_6473.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6474 ->
                let uu___147_6475 = e2 in
                let uu____6476 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___147_6475.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6476;
                  FStar_Syntax_Syntax.pos =
                    (uu___147_6475.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___147_6475.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___148_6485 = env1 in
            let uu____6486 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_6485.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_6485.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_6485.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_6485.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_6485.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_6485.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_6485.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_6485.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_6485.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_6485.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_6485.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_6485.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_6485.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_6485.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_6485.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6486;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_6485.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_6485.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_6485.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_6485.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_6485.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_6485.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_6485.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_6485.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___148_6485.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___148_6485.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___148_6485.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____6487 = check env2 t1 t2 in
          match uu____6487 with
          | None  ->
              let uu____6491 =
                let uu____6492 =
                  let uu____6495 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6496 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6495, uu____6496) in
                FStar_Errors.Error uu____6492 in
              raise uu____6491
          | Some g ->
              ((let uu____6501 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6501
                then
                  let uu____6502 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6502
                else ());
               (let uu____6504 = decorate e t2 in (uu____6504, g)))
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
        let uu____6528 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6528
        then
          let uu____6531 = discharge g1 in
          let uu____6532 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6531, uu____6532)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6544 =
               let uu____6545 =
                 let uu____6546 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6546 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6545
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6544
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6548 = destruct_comp c1 in
           match uu____6548 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6560 = FStar_TypeChecker_Env.get_range env in
                 let uu____6561 =
                   let uu____6562 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6563 =
                     let uu____6564 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6565 =
                       let uu____6567 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6567] in
                     uu____6564 :: uu____6565 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6562 uu____6563 in
                 uu____6561
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6560 in
               ((let uu____6573 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6573
                 then
                   let uu____6574 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6574
                 else ());
                (let g2 =
                   let uu____6577 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6577 in
                 let uu____6578 = discharge g2 in
                 let uu____6579 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6578, uu____6579))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6603 =
        match uu___104_6603 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6609)::[] -> f fst1
        | uu____6622 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6627 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6627
          (fun _0_43  -> FStar_TypeChecker_Common.NonTrivial _0_43) in
      let op_or_e e =
        let uu____6636 =
          let uu____6639 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6639 in
        FStar_All.pipe_right uu____6636
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_t t =
        let uu____6650 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6650
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let short_op_ite uu___105_6664 =
        match uu___105_6664 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6670)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6685)::[] ->
            let uu____6706 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6706
              (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
        | uu____6711 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6718 =
          let uu____6723 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6723) in
        let uu____6728 =
          let uu____6734 =
            let uu____6739 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6739) in
          let uu____6744 =
            let uu____6750 =
              let uu____6755 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6755) in
            let uu____6760 =
              let uu____6766 =
                let uu____6771 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6771) in
              let uu____6776 =
                let uu____6782 =
                  let uu____6787 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6787) in
                [uu____6782; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6766 :: uu____6776 in
            uu____6750 :: uu____6760 in
          uu____6734 :: uu____6744 in
        uu____6718 :: uu____6728 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6828 =
            FStar_Util.find_map table
              (fun uu____6834  ->
                 match uu____6834 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6847 = mk1 seen_args in Some uu____6847
                     else None) in
          (match uu____6828 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6850 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6854 =
      let uu____6855 = FStar_Syntax_Util.un_uinst l in
      uu____6855.FStar_Syntax_Syntax.n in
    match uu____6854 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6859 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6877)::uu____6878 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6884 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6888,Some (FStar_Syntax_Syntax.Implicit uu____6889))::uu____6890
          -> bs
      | uu____6899 ->
          let uu____6900 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6900 with
           | None  -> bs
           | Some t ->
               let uu____6903 =
                 let uu____6904 = FStar_Syntax_Subst.compress t in
                 uu____6904.FStar_Syntax_Syntax.n in
               (match uu____6903 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6908) ->
                    let uu____6919 =
                      FStar_Util.prefix_until
                        (fun uu___106_6938  ->
                           match uu___106_6938 with
                           | (uu____6942,Some (FStar_Syntax_Syntax.Implicit
                              uu____6943)) -> false
                           | uu____6945 -> true) bs' in
                    (match uu____6919 with
                     | None  -> bs
                     | Some ([],uu____6963,uu____6964) -> bs
                     | Some (imps,uu____7001,uu____7002) ->
                         let uu____7039 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7047  ->
                                   match uu____7047 with
                                   | (x,uu____7052) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7039
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7075  ->
                                     match uu____7075 with
                                     | (x,i) ->
                                         let uu____7086 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7086, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7092 -> bs))
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
              (let uu____7111 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7111 e.FStar_Syntax_Syntax.pos)
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
          let uu____7133 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7133
          then e
          else
            (let uu____7135 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7135
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
        (let uu____7161 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7161
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7163 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7163))
         else ());
        (let fv =
           let uu____7166 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7166 None in
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
         let uu____7173 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___149_7182 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_7182.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_7182.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_7182.FStar_Syntax_Syntax.sigmeta)
           }), uu____7173))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7192 =
        match uu___107_7192 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7193 -> false in
      let reducibility uu___108_7197 =
        match uu___108_7197 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7198 -> false in
      let assumption uu___109_7202 =
        match uu___109_7202 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7203 -> false in
      let reification uu___110_7207 =
        match uu___110_7207 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7208 -> true
        | uu____7209 -> false in
      let inferred uu___111_7213 =
        match uu___111_7213 with
        | FStar_Syntax_Syntax.Discriminator uu____7214 -> true
        | FStar_Syntax_Syntax.Projector uu____7215 -> true
        | FStar_Syntax_Syntax.RecordType uu____7218 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7223 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7228 -> false in
      let has_eq uu___112_7232 =
        match uu___112_7232 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7233 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7267 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7270 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7273 =
        let uu____7274 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7276  ->
                  match uu___113_7276 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7277 -> false)) in
        FStar_All.pipe_right uu____7274 Prims.op_Negation in
      if uu____7273
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7287 =
            let uu____7288 =
              let uu____7291 =
                let uu____7292 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7292 msg in
              (uu____7291, r) in
            FStar_Errors.Error uu____7288 in
          raise uu____7287 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7300 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7308 =
            let uu____7309 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7309 in
          if uu____7308 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7313),uu____7314,uu____7315) ->
              ((let uu____7326 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7326
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7329 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7329
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7333 ->
              let uu____7338 =
                let uu____7339 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7339 in
              if uu____7338 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7343 ->
              let uu____7347 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7347 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7350 ->
              let uu____7353 =
                let uu____7354 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7354 in
              if uu____7353 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7358 ->
              let uu____7359 =
                let uu____7360 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7360 in
              if uu____7359 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7364 ->
              let uu____7365 =
                let uu____7366 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7366 in
              if uu____7365 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7370 ->
              let uu____7377 =
                let uu____7378 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7378 in
              if uu____7377 then err'1 () else ()
          | uu____7382 -> ()))
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
                          let uu____7439 =
                            let uu____7442 =
                              let uu____7443 =
                                let uu____7448 =
                                  let uu____7449 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7449 in
                                (uu____7448, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7443 in
                            FStar_Syntax_Syntax.mk uu____7442 in
                          uu____7439 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7475  ->
                                  match uu____7475 with
                                  | (x,imp) ->
                                      let uu____7482 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7482, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7486 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7486 in
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
                             let uu____7495 =
                               let uu____7496 =
                                 let uu____7497 =
                                   let uu____7498 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7499 =
                                     let uu____7500 =
                                       let uu____7501 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7501 in
                                     [uu____7500] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7498
                                     uu____7499 in
                                 uu____7497 None p in
                               FStar_Syntax_Util.b2t uu____7496 in
                             FStar_Syntax_Util.refine x uu____7495 in
                           let uu____7506 =
                             let uu___150_7507 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_7507.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_7507.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7506) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7517 =
                          FStar_List.map
                            (fun uu____7527  ->
                               match uu____7527 with
                               | (x,uu____7534) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7517 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7558  ->
                                match uu____7558 with
                                | (x,uu____7565) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7574 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7574)
                               ||
                               (let uu____7575 =
                                  let uu____7576 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7576.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7575) in
                           let quals =
                             let uu____7579 =
                               let uu____7581 =
                                 let uu____7583 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7583
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7586 =
                                 FStar_List.filter
                                   (fun uu___114_7588  ->
                                      match uu___114_7588 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7589 -> false) iquals in
                               FStar_List.append uu____7581 uu____7586 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7579 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7602 =
                                 let uu____7603 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7603 in
                               FStar_Syntax_Syntax.mk_Total uu____7602 in
                             let uu____7604 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7604 in
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
                           (let uu____7607 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7607
                            then
                              let uu____7608 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7608
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
                                             fun uu____7636  ->
                                               match uu____7636 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7652 =
                                                       let uu____7655 =
                                                         let uu____7656 =
                                                           let uu____7661 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7661,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7656 in
                                                       pos uu____7655 in
                                                     (uu____7652, b)
                                                   else
                                                     (let uu____7665 =
                                                        let uu____7668 =
                                                          let uu____7669 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7669 in
                                                        pos uu____7668 in
                                                      (uu____7665, b)))) in
                                   let pat_true =
                                     let uu____7681 =
                                       let uu____7684 =
                                         let uu____7685 =
                                           let uu____7693 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7693, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7685 in
                                       pos uu____7684 in
                                     (uu____7681, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7715 =
                                       let uu____7718 =
                                         let uu____7719 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7719 in
                                       pos uu____7718 in
                                     (uu____7715, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7728 =
                                     let uu____7731 =
                                       let uu____7732 =
                                         let uu____7748 =
                                           let uu____7750 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7751 =
                                             let uu____7753 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7753] in
                                           uu____7750 :: uu____7751 in
                                         (arg_exp, uu____7748) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7732 in
                                     FStar_Syntax_Syntax.mk uu____7731 in
                                   uu____7728 None p) in
                              let dd =
                                let uu____7764 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7764
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
                                let uu____7771 =
                                  let uu____7774 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7774 in
                                let uu____7775 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7771;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7775
                                } in
                              let impl =
                                let uu____7779 =
                                  let uu____7780 =
                                    let uu____7786 =
                                      let uu____7788 =
                                        let uu____7789 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7789
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7788] in
                                    ((false, [lb]), uu____7786, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7780 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7779;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7804 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7804
                               then
                                 let uu____7805 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7805
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
                                fun uu____7825  ->
                                  match uu____7825 with
                                  | (a,uu____7829) ->
                                      let uu____7830 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7830 with
                                       | (field_name,uu____7834) ->
                                           let field_proj_tm =
                                             let uu____7836 =
                                               let uu____7837 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7837 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7836 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7851 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7860  ->
                                    match uu____7860 with
                                    | (x,uu____7865) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7867 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7867 with
                                         | (field_name,uu____7872) ->
                                             let t =
                                               let uu____7874 =
                                                 let uu____7875 =
                                                   let uu____7878 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7878 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7875 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7874 in
                                             let only_decl =
                                               ((let uu____7880 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7880)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7881 =
                                                    let uu____7882 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7882.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7881) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7892 =
                                                   FStar_List.filter
                                                     (fun uu___115_7894  ->
                                                        match uu___115_7894
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7895 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7892
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_7903  ->
                                                         match uu___116_7903
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7904 ->
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
                                             ((let uu____7907 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7907
                                               then
                                                 let uu____7908 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7908
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
                                                           fun uu____7935  ->
                                                             match uu____7935
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7951
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____7951,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7963
                                                                    =
                                                                    let uu____7966
                                                                    =
                                                                    let uu____7967
                                                                    =
                                                                    let uu____7972
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____7972,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7967 in
                                                                    pos
                                                                    uu____7966 in
                                                                    (uu____7963,
                                                                    b))
                                                                   else
                                                                    (let uu____7976
                                                                    =
                                                                    let uu____7979
                                                                    =
                                                                    let uu____7980
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7980 in
                                                                    pos
                                                                    uu____7979 in
                                                                    (uu____7976,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____7992 =
                                                     let uu____7995 =
                                                       let uu____7996 =
                                                         let uu____8004 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8004,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7996 in
                                                     pos uu____7995 in
                                                   let uu____8010 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____7992, None,
                                                     uu____8010) in
                                                 let body =
                                                   let uu____8021 =
                                                     let uu____8024 =
                                                       let uu____8025 =
                                                         let uu____8041 =
                                                           let uu____8043 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8043] in
                                                         (arg_exp,
                                                           uu____8041) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8025 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8024 in
                                                   uu____8021 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8055 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8055
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
                                                   let uu____8061 =
                                                     let uu____8064 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8064 in
                                                   let uu____8065 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8061;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8065
                                                   } in
                                                 let impl =
                                                   let uu____8069 =
                                                     let uu____8070 =
                                                       let uu____8076 =
                                                         let uu____8078 =
                                                           let uu____8079 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8079
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8078] in
                                                       ((false, [lb]),
                                                         uu____8076, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8070 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8069;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8094 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8094
                                                  then
                                                    let uu____8095 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8095
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7851 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8125) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8128 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8128 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8141 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8141 with
                    | (formals,uu____8151) ->
                        let uu____8162 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8175 =
                                   let uu____8176 =
                                     let uu____8177 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8177 in
                                   FStar_Ident.lid_equals typ_lid uu____8176 in
                                 if uu____8175
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8187,uvs',tps,typ0,uu____8191,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8204 -> failwith "Impossible"
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
                        (match uu____8162 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8246 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8246 with
                              | (indices,uu____8256) ->
                                  let refine_domain =
                                    let uu____8268 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___117_8270  ->
                                              match uu___117_8270 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8271 -> true
                                              | uu____8276 -> false)) in
                                    if uu____8268
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___118_8283 =
                                      match uu___118_8283 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8285,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8292 -> None in
                                    let uu____8293 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8293 with
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
                                    let uu____8301 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8301 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8332  ->
                                               fun uu____8333  ->
                                                 match (uu____8332,
                                                         uu____8333)
                                                 with
                                                 | ((x,uu____8343),(x',uu____8345))
                                                     ->
                                                     let uu____8350 =
                                                       let uu____8355 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8355) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8350) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8356 -> []