open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option* FStar_Syntax_Syntax.lcomp)
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____12 = FStar_TypeChecker_Env.get_range env in
      let uu____13 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.report uu____12 uu____13
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
  =
  fun env  ->
    fun k  -> let uu____59 = new_uvar_aux env k in Prims.fst uu____59
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___94_64  ->
    match uu___94_64 with
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
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____162 ->
              let uu____169 = new_uvar_aux env k in
              (match uu____169 with
               | (t,u) ->
                   let g =
                     let uu___114_181 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u in
                         (reason, env, uu____197, t, k, r) in
                       [uu____190] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___114_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___114_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___114_181.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____182
                     } in
                   let uu____210 =
                     let uu____214 =
                       let uu____217 = as_uvar u in (uu____217, r) in
                     [uu____214] in
                   (t, uu____210, g))
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
              (fun uu____258  ->
                 match uu____258 with
                 | (x,uu____266) -> FStar_Syntax_Print.uvar_to_string x)
              uu____242 in
          FStar_All.pipe_right uu____240 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____283 =
            let uu____284 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____284 in
          FStar_Errors.report r uu____283);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____293 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____293 with
    | None  ->
        let uu____298 =
          let uu____299 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____300 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____299 uu____300 in
        failwith uu____298
    | Some tk -> tk
let force_sort s =
  let uu____315 =
    let uu____318 = force_sort' s in FStar_Syntax_Syntax.mk uu____318 in
  uu____315 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____335  ->
      match uu____335 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____342;
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
                   let uu____374 =
                     let uu____375 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____375.FStar_Syntax_Syntax.n in
                   match uu____374 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____380 = FStar_Syntax_Util.type_u () in
                       (match uu____380 with
                        | (k,uu____386) ->
                            let t2 =
                              let uu____388 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____388 Prims.fst in
                            ((let uu___115_393 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___115_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___115_393.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____394 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____419) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____426) ->
                       (t2, true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____453) ->
                       let uu____476 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____500  ->
                                 fun uu____501  ->
                                   match (uu____500, uu____501) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____543 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____543 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____476 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____604 = aux must_check_ty1 scope body in
                            (match uu____604 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____621 =
                                         FStar_Options.ml_ish () in
                                       if uu____621
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____628 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____628
                                   then
                                     let uu____629 =
                                       FStar_Range.string_of_range r in
                                     let uu____630 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____631 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____629 uu____630 uu____631
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____639 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____647 =
                            let uu____650 =
                              let uu____651 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____651 Prims.fst in
                            FStar_Util.Inl uu____650 in
                          (uu____647, false)) in
                 let uu____658 =
                   let uu____663 = t_binders env in aux false uu____663 e in
                 match uu____658 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____680 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____680
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____684 =
                                let uu____685 =
                                  let uu____688 =
                                    let uu____689 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____689 in
                                  (uu____688, rng) in
                                FStar_Errors.Error uu____685 in
                              Prims.raise uu____684)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____696 ->
               let uu____697 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____697 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
let pat_as_exps:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term
          Prims.list* FStar_Syntax_Syntax.pat)
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____780) ->
              let uu____785 = FStar_Syntax_Util.type_u () in
              (match uu____785 with
               | (k,uu____798) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___116_801 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_801.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_801.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____802 =
                     let uu____805 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____805 t in
                   (match uu____802 with
                    | (e,u) ->
                        let p2 =
                          let uu___117_820 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___117_820.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___117_820.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____827 = FStar_Syntax_Util.type_u () in
              (match uu____827 with
               | (t,uu____840) ->
                   let x1 =
                     let uu___118_842 = x in
                     let uu____843 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___118_842.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___118_842.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____843
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
              let uu____865 = FStar_Syntax_Util.type_u () in
              (match uu____865 with
               | (t,uu____878) ->
                   let x1 =
                     let uu___119_880 = x in
                     let uu____881 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_880.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_880.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____881
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____913 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____969  ->
                        fun uu____970  ->
                          match (uu____969, uu____970) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1069 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1069 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____913 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1177 =
                       let uu____1180 =
                         let uu____1181 =
                           let uu____1186 =
                             let uu____1189 =
                               let uu____1190 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1191 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1190
                                 uu____1191 in
                             uu____1189 None p1.FStar_Syntax_Syntax.p in
                           (uu____1186,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1181 in
                       FStar_Syntax_Syntax.mk uu____1180 in
                     uu____1177 None p1.FStar_Syntax_Syntax.p in
                   let uu____1208 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1214 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1220 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1208, uu____1214, uu____1220, env2, e,
                     (let uu___120_1233 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___120_1233.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___120_1233.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1239 -> failwith "impossible" in
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
                              Prims.raise
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
                                               Prims.raise uu____1535)))
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
                        let uu___121_1651 = p1 in
                        let uu____1654 =
                          let uu____1655 =
                            let uu____1663 = aux f pats1 in (fv, uu____1663) in
                          FStar_Syntax_Syntax.Pat_cons uu____1655 in
                        {
                          FStar_Syntax_Syntax.v = uu____1654;
                          FStar_Syntax_Syntax.ty =
                            (uu___121_1651.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___121_1651.FStar_Syntax_Syntax.p)
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
                   Prims.raise uu____1743
               | uu____1756 -> (b, a, w, arg, p3)) in
        let top_level_pat_as_args env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1799 = one_pat false env1 q in
              (match uu____1799 with
               | (b,a,uu____1815,te,q1) ->
                   let uu____1824 =
                     FStar_List.fold_right
                       (fun p2  ->
                          fun uu____1840  ->
                            match uu____1840 with
                            | (w,args,pats1) ->
                                let uu____1864 = one_pat false env1 p2 in
                                (match uu____1864 with
                                 | (b',a',w',arg,p3) ->
                                     let uu____1890 =
                                       let uu____1891 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a' in
                                       Prims.op_Negation uu____1891 in
                                     if uu____1890
                                     then
                                       let uu____1898 =
                                         let uu____1899 =
                                           let uu____1902 =
                                             FStar_TypeChecker_Err.disjunctive_pattern_vars
                                               a a' in
                                           let uu____1903 =
                                             FStar_TypeChecker_Env.get_range
                                               env1 in
                                           (uu____1902, uu____1903) in
                                         FStar_Errors.Error uu____1899 in
                                       Prims.raise uu____1898
                                     else
                                       (let uu____1911 =
                                          let uu____1913 =
                                            FStar_Syntax_Syntax.as_arg arg in
                                          uu____1913 :: args in
                                        ((FStar_List.append w' w),
                                          uu____1911, (p3 :: pats1))))) pats
                       ([], [], []) in
                   (match uu____1824 with
                    | (w,args,pats1) ->
                        let uu____1934 =
                          let uu____1936 = FStar_Syntax_Syntax.as_arg te in
                          uu____1936 :: args in
                        ((FStar_List.append b w), uu____1934,
                          (let uu___122_1941 = p1 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___122_1941.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___122_1941.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1942 ->
              let uu____1943 = one_pat true env1 p1 in
              (match uu____1943 with
               | (b,uu____1958,uu____1959,arg,p2) ->
                   let uu____1968 =
                     let uu____1970 = FStar_Syntax_Syntax.as_arg arg in
                     [uu____1970] in
                   (b, uu____1968, p2)) in
        let uu____1973 = top_level_pat_as_args env p in
        match uu____1973 with
        | (b,args,p1) ->
            let exps = FStar_All.pipe_right args (FStar_List.map Prims.fst) in
            (b, exps, p1)
let decorate_pattern:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exps  ->
        let qq = p in
        let rec aux p1 e =
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p in
          let e1 = FStar_Syntax_Util.unmeta e in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2044,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2046)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2051,FStar_Syntax_Syntax.Tm_constant uu____2052) ->
              let uu____2053 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____2053
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2057 =
                    let uu____2058 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2059 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2058 uu____2059 in
                  failwith uu____2057)
               else ();
               (let uu____2062 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2062
                then
                  let uu____2063 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2064 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2063
                    uu____2064
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___123_2068 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___123_2068.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___123_2068.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2072 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2072
                then
                  let uu____2073 =
                    let uu____2074 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2075 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2074 uu____2075 in
                  failwith uu____2073
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___124_2079 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___124_2079.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___124_2079.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2081),uu____2082) ->
              let s = force_sort e1 in
              let x1 =
                let uu___125_2091 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___125_2091.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___125_2091.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2104 =
                  let uu____2105 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2105 in
                if uu____2104
                then
                  let uu____2106 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2106
                else ());
               (let uu____2116 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2116))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                FStar_Syntax_Syntax.vars = _;_},args))
            |(FStar_Syntax_Syntax.Pat_cons
              (fv,argpats),FStar_Syntax_Syntax.Tm_app
              ({
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_);
                 FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                 FStar_Syntax_Syntax.vars = _;_},args))
              ->
              ((let uu____2187 =
                  let uu____2188 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2188 Prims.op_Negation in
                if uu____2187
                then
                  let uu____2189 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2189
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2277 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2277
                  | (arg::args2,(argpat,uu____2290)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2340) ->
                           let x =
                             let uu____2356 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2356 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2370) ->
                           let pat =
                             let uu____2385 = aux argpat e2 in
                             let uu____2386 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2385, uu____2386) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2389 ->
                      let uu____2403 =
                        let uu____2404 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2405 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2404 uu____2405 in
                      failwith uu____2403 in
                match_args [] args argpats))
          | uu____2412 ->
              let uu____2415 =
                let uu____2416 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2417 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2418 =
                  let uu____2419 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string) in
                  FStar_All.pipe_right uu____2419
                    (FStar_String.concat "\n\t") in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2416 uu____2417 uu____2418 in
              failwith uu____2415 in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2426) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2442,e::[]) -> aux p e
        | uu____2445 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2482 =
      match uu____2482 with
      | (p,i) ->
          let uu____2492 = decorated_pattern_as_term p in
          (match uu____2492 with
           | (vars,te) ->
               let uu____2505 =
                 let uu____2508 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2508) in
               (vars, uu____2505)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2515 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2523 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2523)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2526 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2526)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2540 =
          let uu____2548 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2548 FStar_List.unzip in
        (match uu____2540 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2606 =
               let uu____2607 =
                 let uu____2608 =
                   let uu____2618 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2618, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2608 in
               mk1 uu____2607 in
             (vars1, uu____2606))
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
      | (wp,uu____2647)::[] -> wp
      | uu____2660 ->
          let uu____2666 =
            let uu____2667 =
              let uu____2668 =
                FStar_List.map
                  (fun uu____2672  ->
                     match uu____2672 with
                     | (x,uu____2676) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2668 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2667 in
          failwith uu____2666 in
    let uu____2680 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2680, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2694 = destruct_comp c in
        match uu____2694 with
        | (u,uu____2699,wp) ->
            let uu____2701 =
              let uu____2707 =
                let uu____2708 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2708 in
              [uu____2707] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2701;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2718 =
          let uu____2722 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2723 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2722 uu____2723 in
        match uu____2718 with | (m,uu____2725,uu____2726) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2736 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2736
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
        let uu____2761 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2761 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2783 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2783 with
             | (a,kwp) ->
                 let uu____2800 = destruct_comp m1 in
                 let uu____2804 = destruct_comp m2 in
                 ((md, a, kwp), uu____2800, uu____2804))
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
            let uu____2852 =
              let uu____2853 =
                let uu____2859 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2859] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2853;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2852
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
      let uu___126_2895 = lc in
      let uu____2896 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___126_2895.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2896;
        FStar_Syntax_Syntax.cflags =
          (uu___126_2895.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2899  ->
             let uu____2900 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2900)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2904 =
      let uu____2905 = FStar_Syntax_Subst.compress t in
      uu____2905.FStar_Syntax_Syntax.n in
    match uu____2904 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2908 -> true
    | uu____2916 -> false
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v1  ->
        let c =
          let uu____2927 =
            let uu____2928 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2928 in
          if uu____2927
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               let uu____2931 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   FStar_Syntax_Const.effect_PURE_lid in
               FStar_Util.must uu____2931 in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2935 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2935
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2937 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2937 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2943 =
                        let uu____2944 =
                          let uu____2945 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2946 =
                            let uu____2947 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2948 =
                              let uu____2950 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2950] in
                            uu____2947 :: uu____2948 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2945 uu____2946 in
                        uu____2944 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2943) in
             (mk_comp m) u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2956 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2956
         then
           let uu____2957 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2958 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2959 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2957
             uu____2958 uu____2959
         else ());
        c
let bind:
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term Prims.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____2976  ->
            match uu____2976 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2986 =
                    FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                  if uu____2986
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____2989 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____2991 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2992 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2989 uu____2991 bstr uu____2992
                  else ());
                 (let bind_it uu____2997 =
                    let uu____2998 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2998
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3008 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme in
                        if uu____3008
                        then
                          let uu____3009 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3011 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3012 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3013 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3014 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3009 uu____3011 uu____3012 uu____3013
                            uu____3014
                        else ());
                       (let try_simplify uu____3022 =
                          let aux uu____3031 =
                            let uu____3032 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3032
                            then
                              match b with
                              | None  -> Some (c2, "trivial no binder")
                              | Some uu____3049 ->
                                  let uu____3050 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3050
                                   then Some (c2, "trivial ml")
                                   else None)
                            else
                              (let uu____3068 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3068
                               then Some (c2, "both ml")
                               else None) in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3101 =
                                  let uu____3104 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3104, reason) in
                                Some uu____3101
                            | uu____3107 -> aux () in
                          let uu____3112 =
                            (FStar_Syntax_Util.is_total_comp c1) &&
                              (FStar_Syntax_Util.is_total_comp c2) in
                          if uu____3112
                          then subst_c2 "both total"
                          else
                            (let uu____3117 =
                               (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                 (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                             if uu____3117
                             then
                               let uu____3121 =
                                 let uu____3124 =
                                   FStar_Syntax_Syntax.mk_GTotal
                                     (FStar_Syntax_Util.comp_result c2) in
                                 (uu____3124, "both gtot") in
                               Some uu____3121
                             else
                               (match (e1opt, b) with
                                | (Some e,Some x) ->
                                    let uu____3137 =
                                      (FStar_Syntax_Util.is_total_comp c1) &&
                                        (let uu____3138 =
                                           FStar_Syntax_Syntax.is_null_bv x in
                                         Prims.op_Negation uu____3138) in
                                    if uu____3137
                                    then subst_c2 "substituted e"
                                    else aux ()
                                | uu____3143 -> aux ())) in
                        let uu____3148 = try_simplify () in
                        match uu____3148 with
                        | Some (c,reason) -> c
                        | None  ->
                            let uu____3158 = lift_and_destruct env c1 c2 in
                            (match uu____3158 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3192 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3192]
                                   | Some x ->
                                       let uu____3194 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3194] in
                                 let mk_lam wp =
                                   FStar_Syntax_Util.abs bs wp
                                     (Some
                                        (FStar_Util.Inr
                                           (FStar_Syntax_Const.effect_Tot_lid,
                                             [FStar_Syntax_Syntax.TOTAL]))) in
                                 let r11 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))) None
                                     r1 in
                                 let wp_args =
                                   let uu____3221 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3222 =
                                     let uu____3224 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3225 =
                                       let uu____3227 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3228 =
                                         let uu____3230 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3231 =
                                           let uu____3233 =
                                             let uu____3234 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3234 in
                                           [uu____3233] in
                                         uu____3230 :: uu____3231 in
                                       uu____3227 :: uu____3228 in
                                     uu____3224 :: uu____3225 in
                                   uu____3221 :: uu____3222 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3239 =
                                     let uu____3240 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3240
                                       wp_args in
                                   uu____3239 None t2.FStar_Syntax_Syntax.pos in
                                 let c = (mk_comp md) u_t2 t2 wp [] in c))) in
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
        (FStar_Syntax_Syntax.mk
           (FStar_Syntax_Syntax.Tm_meta
              (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false)))))
          None f.FStar_Syntax_Syntax.pos
let label_opt:
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) Prims.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | None  -> f
          | Some reason1 ->
              let uu____3289 =
                let uu____3290 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3290 in
              if uu____3289
              then f
              else (let uu____3292 = reason1 () in label uu____3292 r f)
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
            let uu___127_3303 = g in
            let uu____3304 =
              let uu____3305 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3305 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3304;
              FStar_TypeChecker_Env.deferred =
                (uu___127_3303.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___127_3303.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___127_3303.FStar_TypeChecker_Env.implicits)
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
      | uu____3315 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3332 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3336 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3336
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3343 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3343
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3348 = destruct_comp c1 in
                    match uu____3348 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3361 =
                            let uu____3362 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3363 =
                              let uu____3364 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3365 =
                                let uu____3367 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3368 =
                                  let uu____3370 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3370] in
                                uu____3367 :: uu____3368 in
                              uu____3364 :: uu____3365 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3362
                              uu____3363 in
                          uu____3361 None wp.FStar_Syntax_Syntax.pos in
                        (mk_comp md) u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___128_3375 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___128_3375.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___128_3375.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___128_3375.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = weaken
        }
let strengthen_precondition:
  (Prims.unit -> Prims.string) Prims.option ->
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
            let uu____3402 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3402
            then (lc, g0)
            else
              ((let uu____3407 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3407
                then
                  let uu____3408 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3409 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3408 uu____3409
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___95_3415  ->
                          match uu___95_3415 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3417 -> [])) in
                let strengthen uu____3423 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3431 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3431 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3438 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3439 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3439) in
                           if uu____3438
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3446 =
                                 let uu____3447 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3447 in
                               FStar_Syntax_Util.comp_set_flags uu____3446
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3452 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3452
                           then
                             let uu____3453 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3454 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3453 uu____3454
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3457 = destruct_comp c2 in
                           match uu____3457 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3470 =
                                   let uu____3471 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3472 =
                                     let uu____3473 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3474 =
                                       let uu____3476 =
                                         let uu____3477 =
                                           let uu____3478 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3478 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3477 in
                                       let uu____3479 =
                                         let uu____3481 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3481] in
                                       uu____3476 :: uu____3479 in
                                     uu____3473 :: uu____3474 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3471
                                     uu____3472 in
                                 uu____3470 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3487 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3487
                                 then
                                   let uu____3488 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3488
                                 else ());
                                (let c21 =
                                   (mk_comp md) u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3491 =
                  let uu___129_3492 = lc in
                  let uu____3493 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3494 =
                    let uu____3496 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3497 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3497) in
                    if uu____3496 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3493;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___129_3492.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3494;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3491,
                  (let uu___130_3500 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___130_3500.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___130_3500.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___130_3500.FStar_TypeChecker_Env.implicits)
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
        let uu____3515 =
          let uu____3518 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3519 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3518, uu____3519) in
        match uu____3515 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3528 =
                let uu____3529 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3530 =
                  let uu____3531 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3532 =
                    let uu____3534 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3534] in
                  uu____3531 :: uu____3532 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3529 uu____3530 in
              uu____3528 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3542 =
                let uu____3543 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3544 =
                  let uu____3545 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3546 =
                    let uu____3548 =
                      let uu____3549 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3549 in
                    let uu____3550 =
                      let uu____3552 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3552] in
                    uu____3548 :: uu____3550 in
                  uu____3545 :: uu____3546 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3543 uu____3544 in
              uu____3542 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3560 =
                let uu____3561 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3562 =
                  let uu____3563 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3564 =
                    let uu____3566 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3567 =
                      let uu____3569 =
                        let uu____3570 =
                          let uu____3571 =
                            let uu____3575 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3575] in
                          FStar_Syntax_Util.abs uu____3571 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3570 in
                      [uu____3569] in
                    uu____3566 :: uu____3567 in
                  uu____3563 :: uu____3564 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3561 uu____3562 in
              uu____3560 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              (mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3591 = FStar_TypeChecker_Env.get_range env in
              bind uu____3591 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3609 =
            let uu____3610 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3610
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3613 =
                 let uu____3626 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3627 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3626 uu____3627 in
               match uu____3613 with
               | ((md,uu____3629,uu____3630),(u_res_t,res_t,wp_then),
                  (uu____3634,uu____3635,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3664 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3665 =
                       let uu____3666 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3667 =
                         let uu____3668 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3669 =
                           let uu____3671 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3672 =
                             let uu____3674 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3675 =
                               let uu____3677 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3677] in
                             uu____3674 :: uu____3675 in
                           uu____3671 :: uu____3672 in
                         uu____3668 :: uu____3669 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3666 uu____3667 in
                     uu____3665 None uu____3664 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3685 =
                     let uu____3686 = FStar_Options.split_cases () in
                     uu____3686 > (Prims.parse_int "0") in
                   if uu____3685
                   then
                     let comp = (mk_comp md) u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3692 =
                          let uu____3693 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3694 =
                            let uu____3695 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3696 =
                              let uu____3698 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3698] in
                            uu____3695 :: uu____3696 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3693 uu____3694 in
                        uu____3692 None wp.FStar_Syntax_Syntax.pos in
                      (mk_comp md) u_res_t res_t wp1 [])) in
          let uu____3703 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3703;
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
      let uu____3710 =
        let uu____3711 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3711 in
      FStar_Syntax_Syntax.fvar uu____3710 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3731  ->
                 match uu____3731 with
                 | (uu____3734,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3739 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3741 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3741
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3761 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3762 =
                 let uu____3763 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3764 =
                   let uu____3765 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3766 =
                     let uu____3768 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3769 =
                       let uu____3771 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3772 =
                         let uu____3774 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3774] in
                       uu____3771 :: uu____3772 in
                     uu____3768 :: uu____3769 in
                   uu____3765 :: uu____3766 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3763 uu____3764 in
               uu____3762 None uu____3761 in
             let default_case =
               let post_k =
                 let uu____3783 =
                   let uu____3787 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3787] in
                 let uu____3788 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3783 uu____3788 in
               let kwp =
                 let uu____3794 =
                   let uu____3798 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3798] in
                 let uu____3799 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3794 uu____3799 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3804 =
                   let uu____3808 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3808] in
                 let uu____3809 =
                   let uu____3810 =
                     let uu____3813 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3813 in
                   let uu____3814 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3810 uu____3814 in
                 FStar_Syntax_Util.abs uu____3804 uu____3809
                   (Some
                      (FStar_Util.Inr
                         (FStar_Syntax_Const.effect_Tot_lid,
                           [FStar_Syntax_Syntax.TOTAL]))) in
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   FStar_Syntax_Const.effect_PURE_lid in
               (mk_comp md) u_res_t res_t wp [] in
             let comp =
               FStar_List.fold_right
                 (fun uu____3828  ->
                    fun celse  ->
                      match uu____3828 with
                      | (g,cthen) ->
                          let uu____3834 =
                            let uu____3847 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3847 celse in
                          (match uu____3834 with
                           | ((md,uu____3849,uu____3850),(uu____3851,uu____3852,wp_then),
                              (uu____3854,uu____3855,wp_else)) ->
                               let uu____3866 =
                                 ifthenelse md res_t g wp_then wp_else in
                               (mk_comp md) u_res_t res_t uu____3866 []))
                 lcases default_case in
             let uu____3867 =
               let uu____3868 = FStar_Options.split_cases () in
               uu____3868 > (Prims.parse_int "0") in
             if uu____3867
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3872 = destruct_comp comp1 in
                match uu____3872 with
                | (uu____3876,uu____3877,wp) ->
                    let wp1 =
                      let uu____3882 =
                        let uu____3883 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3884 =
                          let uu____3885 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3886 =
                            let uu____3888 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3888] in
                          uu____3885 :: uu____3886 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3883 uu____3884 in
                      uu____3882 None wp.FStar_Syntax_Syntax.pos in
                    (mk_comp md) u_res_t res_t wp1 [])) in
        {
          FStar_Syntax_Syntax.eff_name = eff;
          FStar_Syntax_Syntax.res_typ = res_t;
          FStar_Syntax_Syntax.cflags = [];
          FStar_Syntax_Syntax.comp = bind_cases
        }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let close1 uu____3909 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3913 = FStar_Syntax_Util.is_ml_comp c in
          if uu____3913
          then c
          else
            (let uu____3917 =
               env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
             if uu____3917
             then c
             else
               (let close_wp u_res md res_t bvs1 wp0 =
                  FStar_List.fold_right
                    (fun x  ->
                       fun wp  ->
                         let bs =
                           let uu____3949 = FStar_Syntax_Syntax.mk_binder x in
                           [uu____3949] in
                         let us =
                           let uu____3952 =
                             let uu____3954 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 x.FStar_Syntax_Syntax.sort in
                             [uu____3954] in
                           u_res :: uu____3952 in
                         let wp1 =
                           FStar_Syntax_Util.abs bs wp
                             (Some
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))) in
                         let uu____3965 =
                           let uu____3966 =
                             FStar_TypeChecker_Env.inst_effect_fun_with us
                               env md md.FStar_Syntax_Syntax.close_wp in
                           let uu____3967 =
                             let uu____3968 =
                               FStar_Syntax_Syntax.as_arg res_t in
                             let uu____3969 =
                               let uu____3971 =
                                 FStar_Syntax_Syntax.as_arg
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____3972 =
                                 let uu____3974 =
                                   FStar_Syntax_Syntax.as_arg wp1 in
                                 [uu____3974] in
                               uu____3971 :: uu____3972 in
                             uu____3968 :: uu____3969 in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3966
                             uu____3967 in
                         uu____3965 None wp0.FStar_Syntax_Syntax.pos) bvs1
                    wp0 in
                let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                let uu____3980 = destruct_comp c1 in
                match uu____3980 with
                | (u_res_t,res_t,wp) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c1.FStar_Syntax_Syntax.effect_name in
                    let wp1 = close_wp u_res_t md res_t bvs wp in
                    (mk_comp md) u_res_t c1.FStar_Syntax_Syntax.result_typ
                      wp1 c1.FStar_Syntax_Syntax.flags)) in
        let uu___131_3991 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___131_3991.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___131_3991.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___131_3991.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = close1
        }
let maybe_assume_result_eq_pure_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let refine1 uu____4006 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4010 =
            (let uu____4011 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4011) || env.FStar_TypeChecker_Env.lax in
          if uu____4010
          then c
          else
            (let uu____4015 = FStar_Syntax_Util.is_partial_return c in
             if uu____4015
             then c
             else
               (let uu____4019 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____4020 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid in
                     Prims.op_Negation uu____4020) in
                if uu____4019
                then
                  let uu____4023 =
                    let uu____4024 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                    let uu____4025 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format2 "%s: %s\n" uu____4024 uu____4025 in
                  failwith uu____4023
                else
                  (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                   let t = c1.FStar_Syntax_Syntax.result_typ in
                   let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret1 =
                     let uu____4037 =
                       let uu____4040 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4040
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4037 in
                   let eq1 =
                     let uu____4044 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4044 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let c3 =
                     let uu____4049 =
                       let uu____4050 =
                         let uu____4055 =
                           bind e.FStar_Syntax_Syntax.pos env None
                             (FStar_Syntax_Util.lcomp_of_comp c2)
                             ((Some x), eq_ret) in
                         uu____4055.FStar_Syntax_Syntax.comp in
                       uu____4050 () in
                     FStar_Syntax_Util.comp_set_flags uu____4049
                       (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                       (FStar_Syntax_Util.comp_flags c2)) in
                   c3))) in
        let flags =
          let uu____4059 =
            ((let uu____4060 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4060) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4061 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4061) in
          if uu____4059
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let uu___132_4064 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_4064.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_4064.FStar_Syntax_Syntax.res_typ);
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
          let uu____4083 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4083 with
          | None  ->
              let uu____4088 =
                let uu____4089 =
                  let uu____4092 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4093 = FStar_TypeChecker_Env.get_range env in
                  (uu____4092, uu____4093) in
                FStar_Errors.Error uu____4089 in
              Prims.raise uu____4088
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
          let uu____4114 =
            let uu____4115 = FStar_Syntax_Subst.compress t in
            uu____4115.FStar_Syntax_Syntax.n in
          match uu____4114 with
          | FStar_Syntax_Syntax.Tm_type uu____4120 ->
              let uu____4121 =
                let uu____4122 =
                  FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
                uu____4122.FStar_Syntax_Syntax.n in
              (match uu____4121 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____4128 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid in
                   let b2t1 =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None in
                   let lc1 =
                     let uu____4135 =
                       let uu____4136 =
                         let uu____4137 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0 in
                         FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                           uu____4137 in
                       (None, uu____4136) in
                     bind e.FStar_Syntax_Syntax.pos env (Some e) lc
                       uu____4135 in
                   let e1 =
                     let uu____4146 =
                       let uu____4147 =
                         let uu____4148 = FStar_Syntax_Syntax.as_arg e in
                         [uu____4148] in
                       FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4147 in
                     uu____4146
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos in
                   (e1, lc1)
               | uu____4155 -> (e, lc))
          | uu____4156 -> (e, lc)
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
              (let uu____4176 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4176 with
               | Some ed ->
                   FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4180 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4189 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4189, false)
            else
              (let uu____4193 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4193, true)) in
          match gopt with
          | (None ,uu____4199) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___133_4202 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___133_4202.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___133_4202.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___133_4202.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4206 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4206 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___134_4211 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___134_4211.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___134_4211.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___134_4211.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___135_4214 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___135_4214.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___135_4214.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___135_4214.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4220 =
                     let uu____4221 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4221
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4226 =
                          let uu____4227 = FStar_Syntax_Subst.compress f1 in
                          uu____4227.FStar_Syntax_Syntax.n in
                        match uu____4226 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4232,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4234;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4235;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4236;_},uu____4237)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___136_4261 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___136_4261.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___136_4261.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___136_4261.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4262 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4267 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4267
                              then
                                let uu____4268 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4270 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4271 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4268 uu____4269 uu____4270 uu____4271
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4274 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4274 with
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
                                  let uu____4285 = destruct_comp ct in
                                  (match uu____4285 with
                                   | (u_t,uu____4292,uu____4293) ->
                                       let wp =
                                         let uu____4297 =
                                           let uu____4298 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4299 =
                                             let uu____4300 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4301 =
                                               let uu____4303 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4303] in
                                             uu____4300 :: uu____4301 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4298 uu____4299 in
                                         uu____4297
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4309 =
                                           (mk_comp md) u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4309 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4319 =
                                             let uu____4320 =
                                               let uu____4321 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4321] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4320 in
                                           uu____4319
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4327 =
                                         let uu____4330 =
                                           FStar_All.pipe_left
                                             (fun _0_28  -> Some _0_28)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4341 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4342 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4330
                                           uu____4341 e cret uu____4342 in
                                       (match uu____4327 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___137_4348 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___137_4348.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___137_4348.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4350 =
                                                let uu____4351 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4351 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4350
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4361 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4361
                                              then
                                                let uu____4362 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4362
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___96_4368  ->
                             match uu___96_4368 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4370 -> [])) in
                   let lc1 =
                     let uu___138_4372 = lc in
                     let uu____4373 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4373;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___139_4375 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4375.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4375.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4375.FStar_TypeChecker_Env.implicits)
                     } in
                   (e, lc1, g2))
let pure_or_ghost_pre_and_post:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ Prims.option* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t in
        let uu____4395 =
          let uu____4396 =
            let uu____4397 =
              let uu____4398 =
                let uu____4399 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4399 in
              [uu____4398] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4397 in
          uu____4396 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4395 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4408 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4408
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal _|FStar_Syntax_Syntax.Total _ ->
             failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4432)::(ens,uu____4434)::uu____4435 ->
                    let uu____4457 =
                      let uu____4459 = norm req in Some uu____4459 in
                    let uu____4460 =
                      let uu____4461 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4461 in
                    (uu____4457, uu____4460)
                | uu____4463 ->
                    let uu____4469 =
                      let uu____4470 =
                        let uu____4473 =
                          let uu____4474 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4474 in
                        (uu____4473, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4470 in
                    Prims.raise uu____4469)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4484)::uu____4485 ->
                    let uu____4499 =
                      let uu____4502 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left Prims.fst uu____4502 in
                    (match uu____4499 with
                     | (us_r,uu____4519) ->
                         let uu____4520 =
                           let uu____4523 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left Prims.fst uu____4523 in
                         (match uu____4520 with
                          | (us_e,uu____4540) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4543 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4543
                                  us_r in
                              let as_ens =
                                let uu____4545 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4545
                                  us_e in
                              let req =
                                let uu____4549 =
                                  let uu____4550 =
                                    let uu____4551 =
                                      let uu____4558 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4558] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4551 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4550 in
                                uu____4549
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4574 =
                                  let uu____4575 =
                                    let uu____4576 =
                                      let uu____4583 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4583] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4576 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4575 in
                                uu____4574 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4596 =
                                let uu____4598 = norm req in Some uu____4598 in
                              let uu____4599 =
                                let uu____4600 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4600 in
                              (uu____4596, uu____4599)))
                | uu____4602 -> failwith "Impossible"))
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
             let uu____4632 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4632 with
             | (formals,uu____4641) ->
                 let n_implicits =
                   let uu____4653 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4690  ->
                             match uu____4690 with
                             | (uu____4694,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4653 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4766 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4766 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4780 =
                     let uu____4781 =
                       let uu____4784 =
                         let uu____4785 = FStar_Util.string_of_int n_expected in
                         let uu____4789 = FStar_Syntax_Print.term_to_string e in
                         let uu____4790 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4785 uu____4789 uu____4790 in
                       let uu____4794 = FStar_TypeChecker_Env.get_range env in
                       (uu____4784, uu____4794) in
                     FStar_Errors.Error uu____4781 in
                   Prims.raise uu____4780
                 else Some (n_available - n_expected) in
           let decr_inst uu___97_4807 =
             match uu___97_4807 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4826 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4826 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____4887) when
                          _0_29 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4909,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____4928 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____4928 with
                           | (v1,uu____4949,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____4959 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____4959 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5008 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5008)))
                      | (uu____5022,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5046 =
                      let uu____5060 = inst_n_binders t in
                      aux [] uu____5060 bs1 in
                    (match uu____5046 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5098) -> (e, torig, guard)
                          | (uu____5114,[]) when
                              let uu____5130 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5130 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5131 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5150 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5165 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____5177 =
    let uu____5179 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5179
      (FStar_List.map
         (fun u  ->
            let uu____5189 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5189 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5177 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5201 = FStar_Util.set_is_empty x in
      if uu____5201
      then []
      else
        (let s =
           let uu____5206 =
             let uu____5208 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5208 in
           FStar_All.pipe_right uu____5206 FStar_Util.set_elements in
         (let uu____5213 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5213
          then
            let uu____5214 =
              let uu____5215 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5215 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5214
          else ());
         (let r =
            let uu____5223 = FStar_TypeChecker_Env.get_range env in
            Some uu____5223 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5235 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5235
                     then
                       let uu____5236 =
                         let uu____5237 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5237 in
                       let uu____5239 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5240 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5236 uu____5239 uu____5240
                     else ());
                    FStar_Unionfind.change u
                      (Some (FStar_Syntax_Syntax.U_name u_name));
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
        let uu____5258 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5258 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___98_5285 =
  match uu___98_5285 with
  | None  -> ts
  | Some t ->
      let t1 = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange in
      let t2 = FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t1 in
      (FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk
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
        | ([],uu____5326) -> generalized_univ_names
        | (uu____5330,[]) -> explicit_univ_names
        | uu____5334 ->
            let uu____5339 =
              let uu____5340 =
                let uu____5343 =
                  let uu____5344 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5344 in
                (uu____5343, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5340 in
            Prims.raise uu____5339
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
      (let uu____5358 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5358
       then
         let uu____5359 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5359
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5365 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5365
        then
          let uu____5366 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5366
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5371 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5371))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5401 =
        let uu____5402 =
          FStar_Util.for_all
            (fun uu____5407  ->
               match uu____5407 with
               | (uu____5412,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5402 in
      if uu____5401
      then None
      else
        (let norm c =
           (let uu____5435 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5435
            then
              let uu____5436 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5436
            else ());
           (let c1 =
              let uu____5439 = FStar_TypeChecker_Env.should_verify env in
              if uu____5439
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5442 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5442
             then
               let uu____5443 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5443
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5477 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5477 FStar_Util.set_elements in
         let uu____5521 =
           let uu____5539 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5594  ->
                     match uu____5594 with
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
           FStar_All.pipe_right uu____5539 FStar_List.unzip in
         match uu____5521 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5756 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5756
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
                      (fun uu____5798  ->
                         match uu____5798 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5855  ->
                                       match uu____5855 with
                                       | (u,k) ->
                                           let uu____5875 =
                                             FStar_Unionfind.find u in
                                           (match uu____5875 with
                                            | FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  a;
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                              |FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_abs
                                                  (_,{
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_name
                                                         a;
                                                       FStar_Syntax_Syntax.tk
                                                         = _;
                                                       FStar_Syntax_Syntax.pos
                                                         = _;
                                                       FStar_Syntax_Syntax.vars
                                                         = _;_},_);
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____5913 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5921 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____5926 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____5926 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____5950 =
                                                         let uu____5952 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____5952 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5950 kres in
                                                     let t =
                                                       let uu____5955 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____5956 =
                                                         let uu____5963 =
                                                           let uu____5969 =
                                                             let uu____5970 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____5970 in
                                                           FStar_Util.Inl
                                                             uu____5969 in
                                                         Some uu____5963 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5955
                                                         uu____5956 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____5985 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____6003) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env e in
                                   (e1, c1)
                               | uu____6015 ->
                                   let uu____6023 = (e, c) in
                                   (match uu____6023 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Iota;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env e in
                                        let t =
                                          let uu____6035 =
                                            let uu____6036 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6036.FStar_Syntax_Syntax.n in
                                          match uu____6035 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6053 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6053 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6063 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6073 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6073)) in
                             (match uu____5985 with
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
      (let uu____6111 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6111
       then
         let uu____6112 =
           let uu____6113 =
             FStar_List.map
               (fun uu____6118  ->
                  match uu____6118 with
                  | (lb,uu____6123,uu____6124) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6113 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6112
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6134  ->
              match uu____6134 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6149 =
           let uu____6156 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6172  ->
                     match uu____6172 with | (uu____6178,e,c) -> (e, c))) in
           gen env uu____6156 in
         match uu____6149 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6210  ->
                     match uu____6210 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6254  ->
                  fun uu____6255  ->
                    match (uu____6254, uu____6255) with
                    | ((l,uu____6288,uu____6289),(us,e,c)) ->
                        ((let uu____6315 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6315
                          then
                            let uu____6316 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6317 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6318 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6319 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6316 uu____6317 uu____6318 uu____6319
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6338  ->
              match uu____6338 with
              | (l,generalized_univs,t,c) ->
                  let uu____6356 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6356, t, c)) univnames_lecs generalized_lecs)
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
            then FStar_TypeChecker_Rel.try_teq env2 t11 t21
            else
              (let uu____6389 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6389 with
               | None  -> None
               | Some f ->
                   let uu____6393 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6393) in
          let is_var e1 =
            let uu____6399 =
              let uu____6400 = FStar_Syntax_Subst.compress e1 in
              uu____6400.FStar_Syntax_Syntax.n in
            match uu____6399 with
            | FStar_Syntax_Syntax.Tm_name uu____6403 -> true
            | uu____6404 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___140_6426 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___140_6426.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___140_6426.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6427 ->
                let uu___141_6428 = e2 in
                let uu____6429 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_6428.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6429;
                  FStar_Syntax_Syntax.pos =
                    (uu___141_6428.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___141_6428.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___142_6438 = env1 in
            let uu____6439 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___142_6438.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___142_6438.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___142_6438.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___142_6438.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___142_6438.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___142_6438.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___142_6438.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___142_6438.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___142_6438.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___142_6438.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___142_6438.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___142_6438.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___142_6438.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___142_6438.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___142_6438.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6439;
              FStar_TypeChecker_Env.is_iface =
                (uu___142_6438.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___142_6438.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___142_6438.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___142_6438.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___142_6438.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___142_6438.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___142_6438.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___142_6438.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6440 = check env2 t1 t2 in
          match uu____6440 with
          | None  ->
              let uu____6444 =
                let uu____6445 =
                  let uu____6448 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6449 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6448, uu____6449) in
                FStar_Errors.Error uu____6445 in
              Prims.raise uu____6444
          | Some g ->
              ((let uu____6454 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6454
                then
                  let uu____6455 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6455
                else ());
               (let uu____6457 = decorate e t2 in (uu____6457, g)))
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
        let uu____6481 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6481
        then
          let uu____6484 = discharge g1 in
          let uu____6485 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6484, uu____6485)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6497 =
               let uu____6498 =
                 let uu____6499 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6499 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6498
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6497
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6501 = destruct_comp c1 in
           match uu____6501 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6513 = FStar_TypeChecker_Env.get_range env in
                 let uu____6514 =
                   let uu____6515 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6516 =
                     let uu____6517 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6518 =
                       let uu____6520 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6520] in
                     uu____6517 :: uu____6518 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6515 uu____6516 in
                 uu____6514
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6513 in
               ((let uu____6526 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6526
                 then
                   let uu____6527 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6527
                 else ());
                (let g2 =
                   let uu____6530 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6530 in
                 let uu____6531 = discharge g2 in
                 let uu____6532 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6531, uu____6532))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___99_6556 =
        match uu___99_6556 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6562)::[] -> f fst1
        | uu____6575 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6580 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6580
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32) in
      let op_or_e e =
        let uu____6589 =
          let uu____6592 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6592 in
        FStar_All.pipe_right uu____6589
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_or_t t =
        let uu____6603 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6603
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let short_op_ite uu___100_6617 =
        match uu___100_6617 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6623)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6638)::[] ->
            let uu____6659 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6659
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6664 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6671 =
          let uu____6676 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6676) in
        let uu____6681 =
          let uu____6687 =
            let uu____6692 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6692) in
          let uu____6697 =
            let uu____6703 =
              let uu____6708 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6708) in
            let uu____6713 =
              let uu____6719 =
                let uu____6724 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6724) in
              let uu____6729 =
                let uu____6735 =
                  let uu____6740 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6740) in
                [uu____6735; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6719 :: uu____6729 in
            uu____6703 :: uu____6713 in
          uu____6687 :: uu____6697 in
        uu____6671 :: uu____6681 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6781 =
            FStar_Util.find_map table
              (fun uu____6787  ->
                 match uu____6787 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6800 = mk1 seen_args in Some uu____6800
                     else None) in
          (match uu____6781 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6803 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6807 =
      let uu____6808 = FStar_Syntax_Util.un_uinst l in
      uu____6808.FStar_Syntax_Syntax.n in
    match uu____6807 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6812 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6830)::uu____6831 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6837 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6841,Some (FStar_Syntax_Syntax.Implicit uu____6842))::uu____6843
          -> bs
      | uu____6852 ->
          let uu____6853 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6853 with
           | None  -> bs
           | Some t ->
               let uu____6856 =
                 let uu____6857 = FStar_Syntax_Subst.compress t in
                 uu____6857.FStar_Syntax_Syntax.n in
               (match uu____6856 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6861) ->
                    let uu____6872 =
                      FStar_Util.prefix_until
                        (fun uu___101_6891  ->
                           match uu___101_6891 with
                           | (uu____6895,Some (FStar_Syntax_Syntax.Implicit
                              uu____6896)) -> false
                           | uu____6898 -> true) bs' in
                    (match uu____6872 with
                     | None  -> bs
                     | Some ([],uu____6916,uu____6917) -> bs
                     | Some (imps,uu____6954,uu____6955) ->
                         let uu____6992 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7000  ->
                                   match uu____7000 with
                                   | (x,uu____7005) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____6992
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7028  ->
                                     match uu____7028 with
                                     | (x,i) ->
                                         let uu____7039 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7039, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7045 -> bs))
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
              (let uu____7064 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____7064 e.FStar_Syntax_Syntax.pos)
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
          let uu____7090 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7090
          then e
          else
            (let uu____7092 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____7092 e.FStar_Syntax_Syntax.pos)
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
        (let uu____7122 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7122
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7124 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7124))
         else ());
        (let fv =
           let uu____7127 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7127 None in
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
           FStar_Syntax_Syntax.Sig_let
             (lb, FStar_Range.dummyRange, [lident],
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen], []) in
         let uu____7135 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange in
         (sig_ctx, uu____7135))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___102_7157 =
        match uu___102_7157 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7158 -> false in
      let reducibility uu___103_7162 =
        match uu___103_7162 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7163 -> false in
      let assumption uu___104_7167 =
        match uu___104_7167 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7168 -> false in
      let reification uu___105_7172 =
        match uu___105_7172 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7174 -> false in
      let inferred uu___106_7178 =
        match uu___106_7178 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7183 -> false in
      let has_eq uu___107_7187 =
        match uu___107_7187 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7188 -> false in
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
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
          |FStar_Syntax_Syntax.Visible_default 
           |FStar_Syntax_Syntax.Irreducible 
            |FStar_Syntax_Syntax.Abstract 
             |FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq 
            ->
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
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7213 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7216 =
        let uu____7217 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___108_7219  ->
                  match uu___108_7219 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7220 -> false)) in
        FStar_All.pipe_right uu____7217 Prims.op_Negation in
      if uu____7216
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7230 =
            let uu____7231 =
              let uu____7234 =
                let uu____7235 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7235 msg in
              (uu____7234, r) in
            FStar_Errors.Error uu____7231 in
          Prims.raise uu____7230 in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7243 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____7251 =
            let uu____7252 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7252 in
          if uu____7251 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7256),uu____7257,uu____7258,uu____7259,uu____7260)
              ->
              ((let uu____7273 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7273
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____7276 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7276
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7280 ->
              let uu____7288 =
                let uu____7289 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7289 in
              if uu____7288 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7293 ->
              let uu____7300 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7300 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7303 ->
              let uu____7309 =
                let uu____7310 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7310 in
              if uu____7309 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7314 ->
              let uu____7317 =
                let uu____7318 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7318 in
              if uu____7317 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7322 ->
              let uu____7325 =
                let uu____7326 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7326 in
              if uu____7325 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7330 ->
              let uu____7340 =
                let uu____7341 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7341 in
              if uu____7340 then err'1 () else ()
          | uu____7345 -> ()))
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
                          let uu____7402 =
                            let uu____7405 =
                              let uu____7406 =
                                let uu____7411 =
                                  let uu____7412 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7412 in
                                (uu____7411, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7406 in
                            FStar_Syntax_Syntax.mk uu____7405 in
                          uu____7402 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7438  ->
                                  match uu____7438 with
                                  | (x,imp) ->
                                      let uu____7445 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7445, imp))) in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p in
                      let unrefined_arg_binder =
                        let uu____7451 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7451 in
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
                             let uu____7460 =
                               let uu____7461 =
                                 let uu____7462 =
                                   let uu____7463 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7464 =
                                     let uu____7465 =
                                       let uu____7466 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7466 in
                                     [uu____7465] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7463
                                     uu____7464 in
                                 uu____7462 None p in
                               FStar_Syntax_Util.b2t uu____7461 in
                             FStar_Syntax_Util.refine x uu____7460 in
                           let uu____7471 =
                             let uu___143_7472 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___143_7472.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___143_7472.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7471) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7482 =
                          FStar_List.map
                            (fun uu____7492  ->
                               match uu____7492 with
                               | (x,uu____7499) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7482 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7523  ->
                                match uu____7523 with
                                | (x,uu____7530) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7539 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7539)
                               ||
                               (let uu____7540 =
                                  let uu____7541 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7541.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7540) in
                           let quals =
                             let uu____7544 =
                               let uu____7546 =
                                 let uu____7548 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7548
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7551 =
                                 FStar_List.filter
                                   (fun uu___109_7553  ->
                                      match uu___109_7553 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7554 -> false) iquals in
                               FStar_List.append uu____7546 uu____7551 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7544 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7567 =
                                 let uu____7568 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7568 in
                               FStar_Syntax_Syntax.mk_Total uu____7567 in
                             let uu____7569 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7569 in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name)) in
                           (let uu____7573 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7573
                            then
                              let uu____7574 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7574
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
                                             fun uu____7602  ->
                                               match uu____7602 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7618 =
                                                       let uu____7621 =
                                                         let uu____7622 =
                                                           let uu____7627 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7627,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7622 in
                                                       pos uu____7621 in
                                                     (uu____7618, b)
                                                   else
                                                     (let uu____7631 =
                                                        let uu____7634 =
                                                          let uu____7635 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7635 in
                                                        pos uu____7634 in
                                                      (uu____7631, b)))) in
                                   let pat_true =
                                     let uu____7647 =
                                       let uu____7650 =
                                         let uu____7651 =
                                           let uu____7659 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7659, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7651 in
                                       pos uu____7650 in
                                     (uu____7647, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7681 =
                                       let uu____7684 =
                                         let uu____7685 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7685 in
                                       pos uu____7684 in
                                     (uu____7681, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder) in
                                   let uu____7694 =
                                     let uu____7697 =
                                       let uu____7698 =
                                         let uu____7714 =
                                           let uu____7716 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7717 =
                                             let uu____7719 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7719] in
                                           uu____7716 :: uu____7717 in
                                         (arg_exp, uu____7714) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7698 in
                                     FStar_Syntax_Syntax.mk uu____7697 in
                                   uu____7694 None p) in
                              let dd =
                                let uu____7730 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7730
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
                                let uu____7742 =
                                  let uu____7745 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7745 in
                                let uu____7746 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7742;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7746
                                } in
                              let impl =
                                let uu____7750 =
                                  let uu____7759 =
                                    let uu____7761 =
                                      let uu____7762 =
                                        FStar_All.pipe_right
                                          lb.FStar_Syntax_Syntax.lbname
                                          FStar_Util.right in
                                      FStar_All.pipe_right uu____7762
                                        (fun fv  ->
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                    [uu____7761] in
                                  ((false, [lb]), p, uu____7759, quals, []) in
                                FStar_Syntax_Syntax.Sig_let uu____7750 in
                              (let uu____7778 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7778
                               then
                                 let uu____7779 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7779
                               else ());
                              [decl; impl])) in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder) in
                      let binders =
                        FStar_List.append imp_binders [arg_binder] in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7799  ->
                                  match uu____7799 with
                                  | (a,uu____7803) ->
                                      let uu____7804 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7804 with
                                       | (field_name,uu____7808) ->
                                           let field_proj_tm =
                                             let uu____7810 =
                                               let uu____7811 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7811 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7810 inst_univs in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7827 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7836  ->
                                    match uu____7836 with
                                    | (x,uu____7841) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7843 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7843 with
                                         | (field_name,uu____7848) ->
                                             let t =
                                               let uu____7850 =
                                                 let uu____7851 =
                                                   let uu____7854 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7854 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7851 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7850 in
                                             let only_decl =
                                               ((let uu____7856 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7856)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7857 =
                                                    let uu____7858 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7858.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7857) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7868 =
                                                   FStar_List.filter
                                                     (fun uu___110_7870  ->
                                                        match uu___110_7870
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7871 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7868
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___111_7879  ->
                                                         match uu___111_7879
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7880 ->
                                                             false)) in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1) in
                                             let decl =
                                               FStar_Syntax_Syntax.Sig_declare_typ
                                                 (field_name, uvs, t, quals1,
                                                   (FStar_Ident.range_of_lid
                                                      field_name)) in
                                             ((let uu____7884 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7884
                                               then
                                                 let uu____7885 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7885
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
                                                           fun uu____7912  ->
                                                             match uu____7912
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7928
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____7928,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7940
                                                                    =
                                                                    let uu____7943
                                                                    =
                                                                    let uu____7944
                                                                    =
                                                                    let uu____7949
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____7949,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7944 in
                                                                    pos
                                                                    uu____7943 in
                                                                    (uu____7940,
                                                                    b))
                                                                   else
                                                                    (let uu____7953
                                                                    =
                                                                    let uu____7956
                                                                    =
                                                                    let uu____7957
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7957 in
                                                                    pos
                                                                    uu____7956 in
                                                                    (uu____7953,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____7969 =
                                                     let uu____7972 =
                                                       let uu____7973 =
                                                         let uu____7981 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____7981,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7973 in
                                                     pos uu____7972 in
                                                   let uu____7987 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____7969, None,
                                                     uu____7987) in
                                                 let body =
                                                   let uu____7998 =
                                                     let uu____8001 =
                                                       let uu____8002 =
                                                         let uu____8018 =
                                                           let uu____8020 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8020] in
                                                         (arg_exp,
                                                           uu____8018) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8002 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8001 in
                                                   uu____7998 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8037 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8037
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
                                                   let uu____8043 =
                                                     let uu____8046 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8046 in
                                                   let uu____8047 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8043;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8047
                                                   } in
                                                 let impl =
                                                   let uu____8051 =
                                                     let uu____8060 =
                                                       let uu____8062 =
                                                         let uu____8063 =
                                                           FStar_All.pipe_right
                                                             lb.FStar_Syntax_Syntax.lbname
                                                             FStar_Util.right in
                                                         FStar_All.pipe_right
                                                           uu____8063
                                                           (fun fv  ->
                                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                       [uu____8062] in
                                                     ((false, [lb]), p1,
                                                       uu____8060, quals1,
                                                       []) in
                                                   FStar_Syntax_Syntax.Sig_let
                                                     uu____8051 in
                                                 (let uu____8079 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8079
                                                  then
                                                    let uu____8080 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8080
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7827 FStar_List.flatten in
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
          match se with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____8111,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8117 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8117 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8130 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8130 with
                    | (formals,uu____8140) ->
                        let uu____8151 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8164 =
                                   let uu____8165 =
                                     let uu____8166 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8166 in
                                   FStar_Ident.lid_equals typ_lid uu____8165 in
                                 if uu____8164
                                 then
                                   match se1 with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8176,uvs',tps,typ0,uu____8180,constrs,uu____8182,uu____8183)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8197 -> failwith "Impossible"
                                 else None) in
                          match tps_opt with
                          | Some x -> x
                          | None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Syntax_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor", r)) in
                        (match uu____8151 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8239 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8239 with
                              | (indices,uu____8249) ->
                                  let refine_domain =
                                    let uu____8261 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___112_8263  ->
                                              match uu___112_8263 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8264 -> true
                                              | uu____8269 -> false)) in
                                    if uu____8261
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___113_8276 =
                                      match uu___113_8276 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8278,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8285 -> None in
                                    let uu____8286 =
                                      FStar_Util.find_map quals
                                        filter_records in
                                    match uu____8286 with
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
                                    let uu____8294 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8294 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8325  ->
                                               fun uu____8326  ->
                                                 match (uu____8325,
                                                         uu____8326)
                                                 with
                                                 | ((x,uu____8336),(x',uu____8338))
                                                     ->
                                                     let uu____8343 =
                                                       let uu____8348 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8348) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8343) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8349 -> []