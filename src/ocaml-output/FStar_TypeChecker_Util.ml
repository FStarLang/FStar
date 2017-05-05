open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option* FStar_Syntax_Syntax.lcomp)
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
  =
  fun env  ->
    fun k  -> let uu____59 = new_uvar_aux env k in Prims.fst uu____59
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
                     let uu___119_181 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u in
                         (reason, env, uu____197, t, k, r) in
                       [uu____190] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___119_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_181.FStar_TypeChecker_Env.univ_ineqs);
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
          FStar_Errors.err r uu____283);
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
                            ((let uu___120_393 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___120_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___120_393.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____394 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____419) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____426) ->
                       ((Prims.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____472) ->
                       let uu____495 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____519  ->
                                 fun uu____520  ->
                                   match (uu____519, uu____520) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____562 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____562 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____495 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____623 = aux must_check_ty1 scope body in
                            (match uu____623 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____640 =
                                         FStar_Options.ml_ish () in
                                       if uu____640
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____647 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____647
                                   then
                                     let uu____648 =
                                       FStar_Range.string_of_range r in
                                     let uu____649 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____650 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____648 uu____649 uu____650
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____658 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____666 =
                            let uu____669 =
                              let uu____670 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____670 Prims.fst in
                            FStar_Util.Inl uu____669 in
                          (uu____666, false)) in
                 let uu____677 =
                   let uu____682 = t_binders env in aux false uu____682 e in
                 match uu____677 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____699 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____699
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____703 =
                                let uu____704 =
                                  let uu____707 =
                                    let uu____708 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____708 in
                                  (uu____707, rng) in
                                FStar_Errors.Error uu____704 in
                              Prims.raise uu____703)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____715 ->
               let uu____716 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____716 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____799) ->
              let uu____804 = FStar_Syntax_Util.type_u () in
              (match uu____804 with
               | (k,uu____817) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___121_820 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_820.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_820.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____821 =
                     let uu____824 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____824 t in
                   (match uu____821 with
                    | (e,u) ->
                        let p2 =
                          let uu___122_839 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___122_839.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___122_839.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____846 = FStar_Syntax_Util.type_u () in
              (match uu____846 with
               | (t,uu____859) ->
                   let x1 =
                     let uu___123_861 = x in
                     let uu____862 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_861.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_861.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____862
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
              let uu____884 = FStar_Syntax_Util.type_u () in
              (match uu____884 with
               | (t,uu____897) ->
                   let x1 =
                     let uu___124_899 = x in
                     let uu____900 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_899.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_899.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____900
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____932 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____988  ->
                        fun uu____989  ->
                          match (uu____988, uu____989) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1088 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1088 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____932 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1196 =
                       let uu____1199 =
                         let uu____1200 =
                           let uu____1205 =
                             let uu____1208 =
                               let uu____1209 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1210 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1209
                                 uu____1210 in
                             uu____1208 None p1.FStar_Syntax_Syntax.p in
                           (uu____1205,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1200 in
                       FStar_Syntax_Syntax.mk uu____1199 in
                     uu____1196 None p1.FStar_Syntax_Syntax.p in
                   let uu____1227 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1233 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1239 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1227, uu____1233, uu____1239, env2, e,
                     (let uu___125_1252 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___125_1252.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___125_1252.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1258 -> failwith "impossible" in
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
                  (fun uu____1327  ->
                     match uu____1327 with
                     | (p2,imp) ->
                         let uu____1342 = elaborate_pat env1 p2 in
                         (uu____1342, imp)) pats in
              let uu____1347 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1347 with
               | (uu____1356,t) ->
                   let uu____1358 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1358 with
                    | (f,uu____1369) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1444::uu____1445) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1480::uu____1481,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1521  ->
                                      match uu____1521 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1539 =
                                                   let uu____1541 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1541 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1539
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1547 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1547, true)
                                           | uu____1552 ->
                                               let uu____1554 =
                                                 let uu____1555 =
                                                   let uu____1558 =
                                                     let uu____1559 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1559 in
                                                   (uu____1558,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1555 in
                                               Prims.raise uu____1554)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1610,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1611))
                                   when p_imp ->
                                   let uu____1613 = aux formals' pats' in
                                   (p2, true) :: uu____1613
                               | (uu____1625,Some
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
                                   let uu____1636 = aux formals' pats2 in
                                   (p3, true) :: uu____1636
                               | (uu____1648,imp) ->
                                   let uu____1652 =
                                     let uu____1657 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1657) in
                                   let uu____1660 = aux formals' pats' in
                                   uu____1652 :: uu____1660) in
                        let uu___126_1670 = p1 in
                        let uu____1673 =
                          let uu____1674 =
                            let uu____1682 = aux f pats1 in (fv, uu____1682) in
                          FStar_Syntax_Syntax.Pat_cons uu____1674 in
                        {
                          FStar_Syntax_Syntax.v = uu____1673;
                          FStar_Syntax_Syntax.ty =
                            (uu___126_1670.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___126_1670.FStar_Syntax_Syntax.p)
                        }))
          | uu____1693 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1719 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1719 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1749 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1749 with
               | Some x ->
                   let uu____1762 =
                     let uu____1763 =
                       let uu____1766 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1766, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1763 in
                   Prims.raise uu____1762
               | uu____1775 -> (b, a, w, arg, p3)) in
        let top_level_pat_as_args env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1818 = one_pat false env1 q in
              (match uu____1818 with
               | (b,a,uu____1834,te,q1) ->
                   let uu____1843 =
                     FStar_List.fold_right
                       (fun p2  ->
                          fun uu____1859  ->
                            match uu____1859 with
                            | (w,args,pats1) ->
                                let uu____1883 = one_pat false env1 p2 in
                                (match uu____1883 with
                                 | (b',a',w',arg,p3) ->
                                     let uu____1909 =
                                       let uu____1910 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a' in
                                       Prims.op_Negation uu____1910 in
                                     if uu____1909
                                     then
                                       let uu____1917 =
                                         let uu____1918 =
                                           let uu____1921 =
                                             FStar_TypeChecker_Err.disjunctive_pattern_vars
                                               a a' in
                                           let uu____1922 =
                                             FStar_TypeChecker_Env.get_range
                                               env1 in
                                           (uu____1921, uu____1922) in
                                         FStar_Errors.Error uu____1918 in
                                       Prims.raise uu____1917
                                     else
                                       (let uu____1930 =
                                          let uu____1932 =
                                            FStar_Syntax_Syntax.as_arg arg in
                                          uu____1932 :: args in
                                        ((FStar_List.append w' w),
                                          uu____1930, (p3 :: pats1))))) pats
                       ([], [], []) in
                   (match uu____1843 with
                    | (w,args,pats1) ->
                        let uu____1953 =
                          let uu____1955 = FStar_Syntax_Syntax.as_arg te in
                          uu____1955 :: args in
                        ((FStar_List.append b w), uu____1953,
                          (let uu___127_1960 = p1 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___127_1960.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___127_1960.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1961 ->
              let uu____1962 = one_pat true env1 p1 in
              (match uu____1962 with
               | (b,uu____1977,uu____1978,arg,p2) ->
                   let uu____1987 =
                     let uu____1989 = FStar_Syntax_Syntax.as_arg arg in
                     [uu____1989] in
                   (b, uu____1987, p2)) in
        let uu____1992 = top_level_pat_as_args env p in
        match uu____1992 with
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
          | (uu____2063,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2065)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2070,FStar_Syntax_Syntax.Tm_constant uu____2071) ->
              let uu____2072 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____2072
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2076 =
                    let uu____2077 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2078 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2077 uu____2078 in
                  failwith uu____2076)
               else ();
               (let uu____2081 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2081
                then
                  let uu____2082 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2083 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2082
                    uu____2083
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___128_2087 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_2087.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_2087.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2091 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2091
                then
                  let uu____2092 =
                    let uu____2093 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2094 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2093 uu____2094 in
                  failwith uu____2092
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___129_2098 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___129_2098.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___129_2098.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2100),uu____2101) ->
              let s = force_sort e1 in
              let x1 =
                let uu___130_2110 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___130_2110.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___130_2110.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2123 =
                  let uu____2124 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2124 in
                if uu____2123
                then
                  let uu____2125 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2125
                else ());
               (let uu____2135 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2135))
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
              ((let uu____2206 =
                  let uu____2207 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2207 Prims.op_Negation in
                if uu____2206
                then
                  let uu____2208 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2208
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2296 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2296
                  | (arg::args2,(argpat,uu____2309)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2359) ->
                           let x =
                             let uu____2375 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2375 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2389) ->
                           let pat =
                             let uu____2404 = aux argpat e2 in
                             let uu____2405 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2404, uu____2405) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2408 ->
                      let uu____2422 =
                        let uu____2423 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2424 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2423 uu____2424 in
                      failwith uu____2422 in
                match_args [] args argpats))
          | uu____2431 ->
              let uu____2434 =
                let uu____2435 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2436 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2437 =
                  let uu____2438 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string) in
                  FStar_All.pipe_right uu____2438
                    (FStar_String.concat "\n\t") in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2435 uu____2436 uu____2437 in
              failwith uu____2434 in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2445) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2461,e::[]) -> aux p e
        | uu____2464 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2501 =
      match uu____2501 with
      | (p,i) ->
          let uu____2511 = decorated_pattern_as_term p in
          (match uu____2511 with
           | (vars,te) ->
               let uu____2524 =
                 let uu____2527 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2527) in
               (vars, uu____2524)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2534 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2542 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2542)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2545 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2545)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2559 =
          let uu____2567 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2567 FStar_List.unzip in
        (match uu____2559 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2625 =
               let uu____2626 =
                 let uu____2627 =
                   let uu____2637 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2637, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2627 in
               mk1 uu____2626 in
             (vars1, uu____2625))
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
      | (wp,uu____2666)::[] -> wp
      | uu____2679 ->
          let uu____2685 =
            let uu____2686 =
              let uu____2687 =
                FStar_List.map
                  (fun uu____2691  ->
                     match uu____2691 with
                     | (x,uu____2695) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2687 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2686 in
          failwith uu____2685 in
    let uu____2699 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2699, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2713 = destruct_comp c in
        match uu____2713 with
        | (u,uu____2718,wp) ->
            let uu____2720 =
              let uu____2726 =
                let uu____2727 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2727 in
              [uu____2726] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2720;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2737 =
          let uu____2741 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2742 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2741 uu____2742 in
        match uu____2737 with | (m,uu____2744,uu____2745) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2755 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2755
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
        let uu____2780 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2780 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2802 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2802 with
             | (a,kwp) ->
                 let uu____2819 = destruct_comp m1 in
                 let uu____2823 = destruct_comp m2 in
                 ((md, a, kwp), uu____2819, uu____2823))
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
            let uu____2871 =
              let uu____2872 =
                let uu____2878 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2878] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2872;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2871
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
      let uu___131_2914 = lc in
      let uu____2915 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___131_2914.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2915;
        FStar_Syntax_Syntax.cflags =
          (uu___131_2914.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2918  ->
             let uu____2919 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2919)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2923 =
      let uu____2924 = FStar_Syntax_Subst.compress t in
      uu____2924.FStar_Syntax_Syntax.n in
    match uu____2923 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2927 -> true
    | uu____2935 -> false
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v1  ->
        let c =
          let uu____2946 =
            let uu____2947 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2947 in
          if uu____2946
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               let uu____2950 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   FStar_Syntax_Const.effect_PURE_lid in
               FStar_Util.must uu____2950 in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2954 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2954
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2956 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2956 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2962 =
                        let uu____2963 =
                          let uu____2964 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2965 =
                            let uu____2966 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2967 =
                              let uu____2969 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2969] in
                            uu____2966 :: uu____2967 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2964 uu____2965 in
                        uu____2963 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2962) in
             (mk_comp m) u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2975 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2975
         then
           let uu____2976 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2977 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2978 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2976
             uu____2977 uu____2978
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
          fun uu____2995  ->
            match uu____2995 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3005 =
                    FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                  if uu____3005
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3008 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3010 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3011 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3008 uu____3010 bstr uu____3011
                  else ());
                 (let bind_it uu____3016 =
                    let uu____3017 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3017
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3027 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme in
                        if uu____3027
                        then
                          let uu____3028 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3030 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3031 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3032 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3033 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3028 uu____3030 uu____3031 uu____3032
                            uu____3033
                        else ());
                       (let try_simplify uu____3041 =
                          let aux uu____3050 =
                            let uu____3051 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3051
                            then
                              match b with
                              | None  -> Some (c2, "trivial no binder")
                              | Some uu____3068 ->
                                  let uu____3069 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3069
                                   then Some (c2, "trivial ml")
                                   else None)
                            else
                              (let uu____3087 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3087
                               then Some (c2, "both ml")
                               else None) in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3120 =
                                  let uu____3123 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3123, reason) in
                                Some uu____3120
                            | uu____3126 -> aux () in
                          let uu____3131 =
                            (FStar_Syntax_Util.is_total_comp c1) &&
                              (FStar_Syntax_Util.is_total_comp c2) in
                          if uu____3131
                          then subst_c2 "both total"
                          else
                            (let uu____3136 =
                               (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                 (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                             if uu____3136
                             then
                               let uu____3140 =
                                 let uu____3143 =
                                   FStar_Syntax_Syntax.mk_GTotal
                                     (FStar_Syntax_Util.comp_result c2) in
                                 (uu____3143, "both gtot") in
                               Some uu____3140
                             else
                               (match (e1opt, b) with
                                | (Some e,Some x) ->
                                    let uu____3156 =
                                      (FStar_Syntax_Util.is_total_comp c1) &&
                                        (let uu____3157 =
                                           FStar_Syntax_Syntax.is_null_bv x in
                                         Prims.op_Negation uu____3157) in
                                    if uu____3156
                                    then subst_c2 "substituted e"
                                    else aux ()
                                | uu____3162 -> aux ())) in
                        let uu____3167 = try_simplify () in
                        match uu____3167 with
                        | Some (c,reason) -> c
                        | None  ->
                            let uu____3177 = lift_and_destruct env c1 c2 in
                            (match uu____3177 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3211 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3211]
                                   | Some x ->
                                       let uu____3213 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3213] in
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
                                   let uu____3240 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3241 =
                                     let uu____3243 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3244 =
                                       let uu____3246 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3247 =
                                         let uu____3249 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3250 =
                                           let uu____3252 =
                                             let uu____3253 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3253 in
                                           [uu____3252] in
                                         uu____3249 :: uu____3250 in
                                       uu____3246 :: uu____3247 in
                                     uu____3243 :: uu____3244 in
                                   uu____3240 :: uu____3241 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3258 =
                                     let uu____3259 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3259
                                       wp_args in
                                   uu____3258 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3308 =
                let uu____3309 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3309 in
              if uu____3308
              then f
              else (let uu____3311 = reason1 () in label uu____3311 r f)
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
            let uu___132_3322 = g in
            let uu____3323 =
              let uu____3324 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3324 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3323;
              FStar_TypeChecker_Env.deferred =
                (uu___132_3322.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_3322.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_3322.FStar_TypeChecker_Env.implicits)
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
      | uu____3336 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3353 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3357 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3357
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3364 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3364
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3369 = destruct_comp c1 in
                    match uu____3369 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3382 =
                            let uu____3383 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3384 =
                              let uu____3385 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3386 =
                                let uu____3388 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3389 =
                                  let uu____3391 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3391] in
                                uu____3388 :: uu____3389 in
                              uu____3385 :: uu____3386 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3383
                              uu____3384 in
                          uu____3382 None wp.FStar_Syntax_Syntax.pos in
                        (mk_comp md) u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___133_3396 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___133_3396.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___133_3396.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___133_3396.FStar_Syntax_Syntax.cflags);
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
            let uu____3423 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3423
            then (lc, g0)
            else
              ((let uu____3428 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3428
                then
                  let uu____3429 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3430 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3429 uu____3430
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___100_3436  ->
                          match uu___100_3436 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3438 -> [])) in
                let strengthen uu____3444 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3452 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3452 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3459 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3460 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3460) in
                           if uu____3459
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3467 =
                                 let uu____3468 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3468 in
                               FStar_Syntax_Util.comp_set_flags uu____3467
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
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
                                 uu____3491 None wp.FStar_Syntax_Syntax.pos in
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
                                (let c21 =
                                   (mk_comp md) u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3512 =
                  let uu___134_3513 = lc in
                  let uu____3514 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3515 =
                    let uu____3517 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3518 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3518) in
                    if uu____3517 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3514;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___134_3513.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3515;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3512,
                  (let uu___135_3521 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___135_3521.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___135_3521.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___135_3521.FStar_TypeChecker_Env.implicits)
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
        let uu____3536 =
          let uu____3539 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3540 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3539, uu____3540) in
        match uu____3536 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3549 =
                let uu____3550 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3551 =
                  let uu____3552 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3553 =
                    let uu____3555 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3555] in
                  uu____3552 :: uu____3553 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3550 uu____3551 in
              uu____3549 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3563 =
                let uu____3564 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3565 =
                  let uu____3566 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3567 =
                    let uu____3569 =
                      let uu____3570 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3570 in
                    let uu____3571 =
                      let uu____3573 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3573] in
                    uu____3569 :: uu____3571 in
                  uu____3566 :: uu____3567 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3564 uu____3565 in
              uu____3563 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3581 =
                let uu____3582 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3583 =
                  let uu____3584 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3585 =
                    let uu____3587 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3588 =
                      let uu____3590 =
                        let uu____3591 =
                          let uu____3592 =
                            let uu____3593 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3593] in
                          FStar_Syntax_Util.abs uu____3592 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3591 in
                      [uu____3590] in
                    uu____3587 :: uu____3588 in
                  uu____3584 :: uu____3585 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3582 uu____3583 in
              uu____3581 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              (mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3609 = FStar_TypeChecker_Env.get_range env in
              bind uu____3609 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3627 =
            let uu____3628 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3628
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3631 =
                 let uu____3644 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3645 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3644 uu____3645 in
               match uu____3631 with
               | ((md,uu____3647,uu____3648),(u_res_t,res_t,wp_then),
                  (uu____3652,uu____3653,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3682 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3683 =
                       let uu____3684 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3685 =
                         let uu____3686 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3687 =
                           let uu____3689 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3690 =
                             let uu____3692 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3693 =
                               let uu____3695 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3695] in
                             uu____3692 :: uu____3693 in
                           uu____3689 :: uu____3690 in
                         uu____3686 :: uu____3687 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3684 uu____3685 in
                     uu____3683 None uu____3682 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3703 =
                     let uu____3704 = FStar_Options.split_cases () in
                     uu____3704 > (Prims.parse_int "0") in
                   if uu____3703
                   then
                     let comp = (mk_comp md) u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3710 =
                          let uu____3711 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3712 =
                            let uu____3713 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3714 =
                              let uu____3716 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3716] in
                            uu____3713 :: uu____3714 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3711 uu____3712 in
                        uu____3710 None wp.FStar_Syntax_Syntax.pos in
                      (mk_comp md) u_res_t res_t wp1 [])) in
          let uu____3721 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3721;
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
      let uu____3728 =
        let uu____3729 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3729 in
      FStar_Syntax_Syntax.fvar uu____3728 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3749  ->
                 match uu____3749 with
                 | (uu____3752,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3757 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3759 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3759
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3779 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3780 =
                 let uu____3781 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3782 =
                   let uu____3783 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3784 =
                     let uu____3786 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3787 =
                       let uu____3789 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3790 =
                         let uu____3792 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3792] in
                       uu____3789 :: uu____3790 in
                     uu____3786 :: uu____3787 in
                   uu____3783 :: uu____3784 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3781 uu____3782 in
               uu____3780 None uu____3779 in
             let default_case =
               let post_k =
                 let uu____3801 =
                   let uu____3805 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3805] in
                 let uu____3806 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3801 uu____3806 in
               let kwp =
                 let uu____3812 =
                   let uu____3816 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3816] in
                 let uu____3817 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3812 uu____3817 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3822 =
                   let uu____3823 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3823] in
                 let uu____3824 =
                   let uu____3825 =
                     let uu____3828 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3828 in
                   let uu____3829 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3825 uu____3829 in
                 FStar_Syntax_Util.abs uu____3822 uu____3824
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
                 (fun uu____3843  ->
                    fun celse  ->
                      match uu____3843 with
                      | (g,cthen) ->
                          let uu____3849 =
                            let uu____3862 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3862 celse in
                          (match uu____3849 with
                           | ((md,uu____3864,uu____3865),(uu____3866,uu____3867,wp_then),
                              (uu____3869,uu____3870,wp_else)) ->
                               let uu____3881 =
                                 ifthenelse md res_t g wp_then wp_else in
                               (mk_comp md) u_res_t res_t uu____3881 []))
                 lcases default_case in
             let uu____3882 =
               let uu____3883 = FStar_Options.split_cases () in
               uu____3883 > (Prims.parse_int "0") in
             if uu____3882
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3887 = destruct_comp comp1 in
                match uu____3887 with
                | (uu____3891,uu____3892,wp) ->
                    let wp1 =
                      let uu____3897 =
                        let uu____3898 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3899 =
                          let uu____3900 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3901 =
                            let uu____3903 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3903] in
                          uu____3900 :: uu____3901 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3898 uu____3899 in
                      uu____3897 None wp.FStar_Syntax_Syntax.pos in
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
        let close1 uu____3924 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3928 = FStar_Syntax_Util.is_ml_comp c in
          if uu____3928
          then c
          else
            (let uu____3932 =
               env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
             if uu____3932
             then c
             else
               (let close_wp u_res md res_t bvs1 wp0 =
                  FStar_List.fold_right
                    (fun x  ->
                       fun wp  ->
                         let bs =
                           let uu____3964 = FStar_Syntax_Syntax.mk_binder x in
                           [uu____3964] in
                         let us =
                           let uu____3967 =
                             let uu____3969 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 x.FStar_Syntax_Syntax.sort in
                             [uu____3969] in
                           u_res :: uu____3967 in
                         let wp1 =
                           FStar_Syntax_Util.abs bs wp
                             (Some
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))) in
                         let uu____3980 =
                           let uu____3981 =
                             FStar_TypeChecker_Env.inst_effect_fun_with us
                               env md md.FStar_Syntax_Syntax.close_wp in
                           let uu____3982 =
                             let uu____3983 =
                               FStar_Syntax_Syntax.as_arg res_t in
                             let uu____3984 =
                               let uu____3986 =
                                 FStar_Syntax_Syntax.as_arg
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____3987 =
                                 let uu____3989 =
                                   FStar_Syntax_Syntax.as_arg wp1 in
                                 [uu____3989] in
                               uu____3986 :: uu____3987 in
                             uu____3983 :: uu____3984 in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3981
                             uu____3982 in
                         uu____3980 None wp0.FStar_Syntax_Syntax.pos) bvs1
                    wp0 in
                let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                let uu____3995 = destruct_comp c1 in
                match uu____3995 with
                | (u_res_t,res_t,wp) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c1.FStar_Syntax_Syntax.effect_name in
                    let wp1 = close_wp u_res_t md res_t bvs wp in
                    (mk_comp md) u_res_t c1.FStar_Syntax_Syntax.result_typ
                      wp1 c1.FStar_Syntax_Syntax.flags)) in
        let uu___136_4006 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_4006.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_4006.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___136_4006.FStar_Syntax_Syntax.cflags);
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
        let refine1 uu____4021 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4025 =
            (let uu____4026 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4026) || env.FStar_TypeChecker_Env.lax in
          if uu____4025
          then c
          else
            (let uu____4030 = FStar_Syntax_Util.is_partial_return c in
             if uu____4030
             then c
             else
               (let uu____4034 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____4035 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid in
                     Prims.op_Negation uu____4035) in
                if uu____4034
                then
                  let uu____4038 =
                    let uu____4039 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                    let uu____4040 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format2 "%s: %s\n" uu____4039 uu____4040 in
                  failwith uu____4038
                else
                  (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                   let t = c1.FStar_Syntax_Syntax.result_typ in
                   let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret1 =
                     let uu____4052 =
                       let uu____4055 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4055
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4052 in
                   let eq1 =
                     let uu____4059 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4059 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let c3 =
                     let uu____4064 =
                       let uu____4065 =
                         let uu____4070 =
                           bind e.FStar_Syntax_Syntax.pos env None
                             (FStar_Syntax_Util.lcomp_of_comp c2)
                             ((Some x), eq_ret) in
                         uu____4070.FStar_Syntax_Syntax.comp in
                       uu____4065 () in
                     FStar_Syntax_Util.comp_set_flags uu____4064
                       (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                       (FStar_Syntax_Util.comp_flags c2)) in
                   c3))) in
        let flags =
          let uu____4074 =
            ((let uu____4075 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4075) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4076 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4076) in
          if uu____4074
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let uu___137_4079 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4079.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4079.FStar_Syntax_Syntax.res_typ);
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
          let uu____4098 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4098 with
          | None  ->
              let uu____4103 =
                let uu____4104 =
                  let uu____4107 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4108 = FStar_TypeChecker_Env.get_range env in
                  (uu____4107, uu____4108) in
                FStar_Errors.Error uu____4104 in
              Prims.raise uu____4103
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
            let uu____4134 =
              let uu____4135 = FStar_Syntax_Subst.compress t2 in
              uu____4135.FStar_Syntax_Syntax.n in
            match uu____4134 with
            | FStar_Syntax_Syntax.Tm_type uu____4138 -> true
            | uu____4139 -> false in
          let uu____4140 =
            let uu____4141 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4141.FStar_Syntax_Syntax.n in
          match uu____4140 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4147 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4154 =
                  let uu____4155 =
                    let uu____4156 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4156 in
                  (None, uu____4155) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4154 in
              let e1 =
                let uu____4165 =
                  let uu____4166 =
                    let uu____4167 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4167] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4166 in
                uu____4165
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4174 -> (e, lc)
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
              (let uu____4194 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4194 with
               | Some ed ->
                   FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4198 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4207 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4207, false)
            else
              (let uu____4211 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4211, true)) in
          match gopt with
          | (None ,uu____4217) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___138_4220 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___138_4220.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___138_4220.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___138_4220.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4224 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4224 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___139_4229 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_4229.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_4229.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___139_4229.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___140_4232 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___140_4232.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___140_4232.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___140_4232.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4238 =
                     let uu____4239 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4239
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4244 =
                          let uu____4245 = FStar_Syntax_Subst.compress f1 in
                          uu____4245.FStar_Syntax_Syntax.n in
                        match uu____4244 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4250,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4252;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4253;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4254;_},uu____4255)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___141_4279 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___141_4279.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___141_4279.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___141_4279.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4280 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4285 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4285
                              then
                                let uu____4286 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4287 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4288 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4289 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4286 uu____4287 uu____4288 uu____4289
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4292 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4292 with
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
                                  let uu____4303 = destruct_comp ct in
                                  (match uu____4303 with
                                   | (u_t,uu____4310,uu____4311) ->
                                       let wp =
                                         let uu____4315 =
                                           let uu____4316 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4317 =
                                             let uu____4318 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4319 =
                                               let uu____4321 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4321] in
                                             uu____4318 :: uu____4319 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4316 uu____4317 in
                                         uu____4315
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4327 =
                                           (mk_comp md) u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4327 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4337 =
                                             let uu____4338 =
                                               let uu____4339 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4339] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4338 in
                                           uu____4337
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4345 =
                                         let uu____4348 =
                                           FStar_All.pipe_left
                                             (fun _0_28  -> Some _0_28)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4359 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4360 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4348
                                           uu____4359 e cret uu____4360 in
                                       (match uu____4345 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___142_4366 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___142_4366.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___142_4366.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4368 =
                                                let uu____4369 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4369 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4368
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4379 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4379
                                              then
                                                let uu____4380 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4380
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___101_4386  ->
                             match uu___101_4386 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4388 -> [])) in
                   let lc1 =
                     let uu___143_4390 = lc in
                     let uu____4391 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4391;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___144_4393 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_4393.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_4393.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_4393.FStar_TypeChecker_Env.implicits)
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
        let uu____4413 =
          let uu____4414 =
            let uu____4415 =
              let uu____4416 =
                let uu____4417 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4417 in
              [uu____4416] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4415 in
          uu____4414 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4413 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4426 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4426
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
                | (req,uu____4450)::(ens,uu____4452)::uu____4453 ->
                    let uu____4475 =
                      let uu____4477 = norm req in Some uu____4477 in
                    let uu____4478 =
                      let uu____4479 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4479 in
                    (uu____4475, uu____4478)
                | uu____4481 ->
                    let uu____4487 =
                      let uu____4488 =
                        let uu____4491 =
                          let uu____4492 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4492 in
                        (uu____4491, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4488 in
                    Prims.raise uu____4487)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4502)::uu____4503 ->
                    let uu____4517 =
                      let uu____4520 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left Prims.fst uu____4520 in
                    (match uu____4517 with
                     | (us_r,uu____4537) ->
                         let uu____4538 =
                           let uu____4541 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left Prims.fst uu____4541 in
                         (match uu____4538 with
                          | (us_e,uu____4558) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4561 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4561
                                  us_r in
                              let as_ens =
                                let uu____4563 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4563
                                  us_e in
                              let req =
                                let uu____4567 =
                                  let uu____4568 =
                                    let uu____4569 =
                                      let uu____4576 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4576] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4569 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4568 in
                                uu____4567
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4592 =
                                  let uu____4593 =
                                    let uu____4594 =
                                      let uu____4601 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4601] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4594 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4593 in
                                uu____4592 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4614 =
                                let uu____4616 = norm req in Some uu____4616 in
                              let uu____4617 =
                                let uu____4618 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4618 in
                              (uu____4614, uu____4617)))
                | uu____4620 -> failwith "Impossible"))
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
             let uu____4650 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4650 with
             | (formals,uu____4659) ->
                 let n_implicits =
                   let uu____4671 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4708  ->
                             match uu____4708 with
                             | (uu____4712,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4671 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4784 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4784 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4798 =
                     let uu____4799 =
                       let uu____4802 =
                         let uu____4803 = FStar_Util.string_of_int n_expected in
                         let uu____4807 = FStar_Syntax_Print.term_to_string e in
                         let uu____4808 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4803 uu____4807 uu____4808 in
                       let uu____4812 = FStar_TypeChecker_Env.get_range env in
                       (uu____4802, uu____4812) in
                     FStar_Errors.Error uu____4799 in
                   Prims.raise uu____4798
                 else Some (n_available - n_expected) in
           let decr_inst uu___102_4825 =
             match uu___102_4825 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4844 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4844 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____4905) when
                          _0_29 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4927,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____4946 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____4946 with
                           | (v1,uu____4967,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____4977 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____4977 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5026 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5026)))
                      | (uu____5040,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5064 =
                      let uu____5078 = inst_n_binders t in
                      aux [] uu____5078 bs1 in
                    (match uu____5064 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5116) -> (e, torig, guard)
                          | (uu____5132,[]) when
                              let uu____5148 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5148 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5149 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5168 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5183 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____5195 =
    let uu____5197 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5197
      (FStar_List.map
         (fun u  ->
            let uu____5207 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5207 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5195 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5219 = FStar_Util.set_is_empty x in
      if uu____5219
      then []
      else
        (let s =
           let uu____5224 =
             let uu____5226 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5226 in
           FStar_All.pipe_right uu____5224 FStar_Util.set_elements in
         (let uu____5231 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5231
          then
            let uu____5232 =
              let uu____5233 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5233 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5232
          else ());
         (let r =
            let uu____5241 = FStar_TypeChecker_Env.get_range env in
            Some uu____5241 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5253 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5253
                     then
                       let uu____5254 =
                         let uu____5255 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5255 in
                       let uu____5257 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5258 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5254 uu____5257 uu____5258
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
        let uu____5276 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5276 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___103_5303 =
  match uu___103_5303 with
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
        | ([],uu____5344) -> generalized_univ_names
        | (uu____5348,[]) -> explicit_univ_names
        | uu____5352 ->
            let uu____5357 =
              let uu____5358 =
                let uu____5361 =
                  let uu____5362 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5362 in
                (uu____5361, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5358 in
            Prims.raise uu____5357
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
      (let uu____5376 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5376
       then
         let uu____5377 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5377
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5383 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5383
        then
          let uu____5384 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5384
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5389 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5389))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5419 =
        let uu____5420 =
          FStar_Util.for_all
            (fun uu____5425  ->
               match uu____5425 with
               | (uu____5430,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5420 in
      if uu____5419
      then None
      else
        (let norm c =
           (let uu____5453 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5453
            then
              let uu____5454 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5454
            else ());
           (let c1 =
              let uu____5457 = FStar_TypeChecker_Env.should_verify env in
              if uu____5457
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5460 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5460
             then
               let uu____5461 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5461
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5495 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5495 FStar_Util.set_elements in
         let uu____5539 =
           let uu____5557 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5612  ->
                     match uu____5612 with
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
           FStar_All.pipe_right uu____5557 FStar_List.unzip in
         match uu____5539 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5774 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5774
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
                      (fun uu____5816  ->
                         match uu____5816 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5873  ->
                                       match uu____5873 with
                                       | (u,k) ->
                                           let uu____5893 =
                                             FStar_Unionfind.find u in
                                           (match uu____5893 with
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
                                                uu____5931 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5939 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____5944 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____5944 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____5968 =
                                                         let uu____5970 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____5970 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5968 kres in
                                                     let t =
                                                       let uu____5973 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____5974 =
                                                         let uu____5981 =
                                                           let uu____5987 =
                                                             let uu____5988 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____5988 in
                                                           FStar_Util.Inl
                                                             uu____5987 in
                                                         Some uu____5981 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5973
                                                         uu____5974 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6003 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____6021) ->
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
                               | uu____6033 ->
                                   let uu____6041 = (e, c) in
                                   (match uu____6041 with
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
                                          let uu____6053 =
                                            let uu____6054 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6054.FStar_Syntax_Syntax.n in
                                          match uu____6053 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6071 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6071 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6081 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6091 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6091)) in
                             (match uu____6003 with
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
      (let uu____6129 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6129
       then
         let uu____6130 =
           let uu____6131 =
             FStar_List.map
               (fun uu____6136  ->
                  match uu____6136 with
                  | (lb,uu____6141,uu____6142) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6131 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6130
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6152  ->
              match uu____6152 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6167 =
           let uu____6174 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6190  ->
                     match uu____6190 with | (uu____6196,e,c) -> (e, c))) in
           gen env uu____6174 in
         match uu____6167 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6228  ->
                     match uu____6228 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6272  ->
                  fun uu____6273  ->
                    match (uu____6272, uu____6273) with
                    | ((l,uu____6306,uu____6307),(us,e,c)) ->
                        ((let uu____6333 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6333
                          then
                            let uu____6334 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6335 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6336 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6337 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6334 uu____6335 uu____6336 uu____6337
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6356  ->
              match uu____6356 with
              | (l,generalized_univs,t,c) ->
                  let uu____6374 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6374, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6407 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6407 with
               | None  -> None
               | Some f ->
                   let uu____6411 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6411) in
          let is_var e1 =
            let uu____6417 =
              let uu____6418 = FStar_Syntax_Subst.compress e1 in
              uu____6418.FStar_Syntax_Syntax.n in
            match uu____6417 with
            | FStar_Syntax_Syntax.Tm_name uu____6421 -> true
            | uu____6422 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___145_6444 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___145_6444.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___145_6444.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6445 ->
                let uu___146_6446 = e2 in
                let uu____6447 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___146_6446.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6447;
                  FStar_Syntax_Syntax.pos =
                    (uu___146_6446.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___146_6446.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___147_6456 = env1 in
            let uu____6457 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___147_6456.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___147_6456.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___147_6456.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___147_6456.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___147_6456.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___147_6456.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___147_6456.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___147_6456.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___147_6456.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___147_6456.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___147_6456.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___147_6456.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___147_6456.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___147_6456.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___147_6456.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6457;
              FStar_TypeChecker_Env.is_iface =
                (uu___147_6456.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___147_6456.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___147_6456.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___147_6456.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___147_6456.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___147_6456.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___147_6456.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___147_6456.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6458 = check env2 t1 t2 in
          match uu____6458 with
          | None  ->
              let uu____6462 =
                let uu____6463 =
                  let uu____6466 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6467 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6466, uu____6467) in
                FStar_Errors.Error uu____6463 in
              Prims.raise uu____6462
          | Some g ->
              ((let uu____6472 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6472
                then
                  let uu____6473 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6473
                else ());
               (let uu____6475 = decorate e t2 in (uu____6475, g)))
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
        let uu____6499 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6499
        then
          let uu____6502 = discharge g1 in
          let uu____6503 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6502, uu____6503)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6515 =
               let uu____6516 =
                 let uu____6517 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6517 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6516
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6515
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6519 = destruct_comp c1 in
           match uu____6519 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6531 = FStar_TypeChecker_Env.get_range env in
                 let uu____6532 =
                   let uu____6533 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6534 =
                     let uu____6535 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6536 =
                       let uu____6538 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6538] in
                     uu____6535 :: uu____6536 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6533 uu____6534 in
                 uu____6532
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6531 in
               ((let uu____6544 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6544
                 then
                   let uu____6545 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6545
                 else ());
                (let g2 =
                   let uu____6548 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6548 in
                 let uu____6549 = discharge g2 in
                 let uu____6550 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6549, uu____6550))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___104_6574 =
        match uu___104_6574 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6580)::[] -> f fst1
        | uu____6593 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6598 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6598
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32) in
      let op_or_e e =
        let uu____6607 =
          let uu____6610 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6610 in
        FStar_All.pipe_right uu____6607
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_or_t t =
        let uu____6621 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6621
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let short_op_ite uu___105_6635 =
        match uu___105_6635 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6641)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6656)::[] ->
            let uu____6677 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6677
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6682 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6689 =
          let uu____6694 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6694) in
        let uu____6699 =
          let uu____6705 =
            let uu____6710 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6710) in
          let uu____6715 =
            let uu____6721 =
              let uu____6726 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6726) in
            let uu____6731 =
              let uu____6737 =
                let uu____6742 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6742) in
              let uu____6747 =
                let uu____6753 =
                  let uu____6758 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6758) in
                [uu____6753; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6737 :: uu____6747 in
            uu____6721 :: uu____6731 in
          uu____6705 :: uu____6715 in
        uu____6689 :: uu____6699 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6799 =
            FStar_Util.find_map table
              (fun uu____6805  ->
                 match uu____6805 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6818 = mk1 seen_args in Some uu____6818
                     else None) in
          (match uu____6799 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6821 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6825 =
      let uu____6826 = FStar_Syntax_Util.un_uinst l in
      uu____6826.FStar_Syntax_Syntax.n in
    match uu____6825 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6830 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6848)::uu____6849 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6855 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6859,Some (FStar_Syntax_Syntax.Implicit uu____6860))::uu____6861
          -> bs
      | uu____6870 ->
          let uu____6871 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6871 with
           | None  -> bs
           | Some t ->
               let uu____6874 =
                 let uu____6875 = FStar_Syntax_Subst.compress t in
                 uu____6875.FStar_Syntax_Syntax.n in
               (match uu____6874 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6879) ->
                    let uu____6890 =
                      FStar_Util.prefix_until
                        (fun uu___106_6909  ->
                           match uu___106_6909 with
                           | (uu____6913,Some (FStar_Syntax_Syntax.Implicit
                              uu____6914)) -> false
                           | uu____6916 -> true) bs' in
                    (match uu____6890 with
                     | None  -> bs
                     | Some ([],uu____6934,uu____6935) -> bs
                     | Some (imps,uu____6972,uu____6973) ->
                         let uu____7010 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7018  ->
                                   match uu____7018 with
                                   | (x,uu____7023) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7010
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7046  ->
                                     match uu____7046 with
                                     | (x,i) ->
                                         let uu____7057 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7057, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7063 -> bs))
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
              (let uu____7082 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____7082 e.FStar_Syntax_Syntax.pos)
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
          let uu____7108 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7108
          then e
          else
            (let uu____7110 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____7110 e.FStar_Syntax_Syntax.pos)
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
        (let uu____7140 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7140
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7142 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7142))
         else ());
        (let fv =
           let uu____7145 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7145 None in
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
             (FStar_Syntax_Syntax.Sig_let
                (lb, [lident],
                  [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen], [])) in
         let uu____7153 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange in
         (sig_ctx, uu____7153))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___107_7175 =
        match uu___107_7175 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7176 -> false in
      let reducibility uu___108_7180 =
        match uu___108_7180 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7181 -> false in
      let assumption uu___109_7185 =
        match uu___109_7185 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7186 -> false in
      let reification uu___110_7190 =
        match uu___110_7190 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7192 -> false in
      let inferred uu___111_7196 =
        match uu___111_7196 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7201 -> false in
      let has_eq uu___112_7205 =
        match uu___112_7205 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7206 -> false in
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
        | uu____7231 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7234 =
        let uu____7235 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___113_7237  ->
                  match uu___113_7237 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7238 -> false)) in
        FStar_All.pipe_right uu____7235 Prims.op_Negation in
      if uu____7234
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7248 =
            let uu____7249 =
              let uu____7252 =
                let uu____7253 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7253 msg in
              (uu____7252, r) in
            FStar_Errors.Error uu____7249 in
          Prims.raise uu____7248 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7261 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7269 =
            let uu____7270 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7270 in
          if uu____7269 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7274),uu____7275,uu____7276,uu____7277) ->
              ((let uu____7290 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7290
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7293 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7293
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7297 ->
              let uu____7304 =
                let uu____7305 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7305 in
              if uu____7304 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7309 ->
              let uu____7315 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7315 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7318 ->
              let uu____7323 =
                let uu____7324 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7324 in
              if uu____7323 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7328 ->
              let uu____7329 =
                let uu____7330 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7330 in
              if uu____7329 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7334 ->
              let uu____7335 =
                let uu____7336 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7336 in
              if uu____7335 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7340 ->
              let uu____7349 =
                let uu____7350 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7350 in
              if uu____7349 then err'1 () else ()
          | uu____7354 -> ()))
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
                          let uu____7411 =
                            let uu____7414 =
                              let uu____7415 =
                                let uu____7420 =
                                  let uu____7421 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7421 in
                                (uu____7420, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7415 in
                            FStar_Syntax_Syntax.mk uu____7414 in
                          uu____7411 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7447  ->
                                  match uu____7447 with
                                  | (x,imp) ->
                                      let uu____7454 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7454, imp))) in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p in
                      let unrefined_arg_binder =
                        let uu____7460 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7460 in
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
                             let uu____7469 =
                               let uu____7470 =
                                 let uu____7471 =
                                   let uu____7472 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7473 =
                                     let uu____7474 =
                                       let uu____7475 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7475 in
                                     [uu____7474] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7472
                                     uu____7473 in
                                 uu____7471 None p in
                               FStar_Syntax_Util.b2t uu____7470 in
                             FStar_Syntax_Util.refine x uu____7469 in
                           let uu____7480 =
                             let uu___148_7481 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_7481.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_7481.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7480) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7491 =
                          FStar_List.map
                            (fun uu____7501  ->
                               match uu____7501 with
                               | (x,uu____7508) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7491 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7532  ->
                                match uu____7532 with
                                | (x,uu____7539) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7548 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7548)
                               ||
                               (let uu____7549 =
                                  let uu____7550 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7550.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7549) in
                           let quals =
                             let uu____7553 =
                               let uu____7555 =
                                 let uu____7557 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7557
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7560 =
                                 FStar_List.filter
                                   (fun uu___114_7562  ->
                                      match uu___114_7562 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7563 -> false) iquals in
                               FStar_List.append uu____7555 uu____7560 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7553 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7576 =
                                 let uu____7577 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7577 in
                               FStar_Syntax_Syntax.mk_Total uu____7576 in
                             let uu____7578 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7578 in
                           let decl =
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t, quals));
                               FStar_Syntax_Syntax.sigrng =
                                 (FStar_Ident.range_of_lid discriminator_name)
                             } in
                           (let uu____7582 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7582
                            then
                              let uu____7583 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7583
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
                                             fun uu____7611  ->
                                               match uu____7611 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7627 =
                                                       let uu____7630 =
                                                         let uu____7631 =
                                                           let uu____7636 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7636,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7631 in
                                                       pos uu____7630 in
                                                     (uu____7627, b)
                                                   else
                                                     (let uu____7640 =
                                                        let uu____7643 =
                                                          let uu____7644 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7644 in
                                                        pos uu____7643 in
                                                      (uu____7640, b)))) in
                                   let pat_true =
                                     let uu____7656 =
                                       let uu____7659 =
                                         let uu____7660 =
                                           let uu____7668 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7668, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7660 in
                                       pos uu____7659 in
                                     (uu____7656, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7690 =
                                       let uu____7693 =
                                         let uu____7694 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7694 in
                                       pos uu____7693 in
                                     (uu____7690, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder) in
                                   let uu____7703 =
                                     let uu____7706 =
                                       let uu____7707 =
                                         let uu____7723 =
                                           let uu____7725 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7726 =
                                             let uu____7728 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7728] in
                                           uu____7725 :: uu____7726 in
                                         (arg_exp, uu____7723) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7707 in
                                     FStar_Syntax_Syntax.mk uu____7706 in
                                   uu____7703 None p) in
                              let dd =
                                let uu____7739 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7739
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
                                let uu____7751 =
                                  let uu____7754 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7754 in
                                let uu____7755 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7751;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7755
                                } in
                              let impl =
                                let uu____7759 =
                                  let uu____7760 =
                                    let uu____7768 =
                                      let uu____7770 =
                                        let uu____7771 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7771
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7770] in
                                    ((false, [lb]), uu____7768, quals, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7760 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7759;
                                  FStar_Syntax_Syntax.sigrng = p
                                } in
                              (let uu____7787 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7787
                               then
                                 let uu____7788 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7788
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
                                fun uu____7808  ->
                                  match uu____7808 with
                                  | (a,uu____7812) ->
                                      let uu____7813 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7813 with
                                       | (field_name,uu____7817) ->
                                           let field_proj_tm =
                                             let uu____7819 =
                                               let uu____7820 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7820 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7819 inst_univs in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7836 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7845  ->
                                    match uu____7845 with
                                    | (x,uu____7850) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7852 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7852 with
                                         | (field_name,uu____7857) ->
                                             let t =
                                               let uu____7859 =
                                                 let uu____7860 =
                                                   let uu____7863 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7863 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7860 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7859 in
                                             let only_decl =
                                               ((let uu____7865 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7865)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7866 =
                                                    let uu____7867 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7867.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7866) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7877 =
                                                   FStar_List.filter
                                                     (fun uu___115_7879  ->
                                                        match uu___115_7879
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7880 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7877
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___116_7888  ->
                                                         match uu___116_7888
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7889 ->
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
                                                      (field_name, uvs, t,
                                                        quals1));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   (FStar_Ident.range_of_lid
                                                      field_name)
                                               } in
                                             ((let uu____7893 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7893
                                               then
                                                 let uu____7894 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7894
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
                                                           fun uu____7921  ->
                                                             match uu____7921
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7937
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____7937,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7949
                                                                    =
                                                                    let uu____7952
                                                                    =
                                                                    let uu____7953
                                                                    =
                                                                    let uu____7958
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____7958,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7953 in
                                                                    pos
                                                                    uu____7952 in
                                                                    (uu____7949,
                                                                    b))
                                                                   else
                                                                    (let uu____7962
                                                                    =
                                                                    let uu____7965
                                                                    =
                                                                    let uu____7966
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7966 in
                                                                    pos
                                                                    uu____7965 in
                                                                    (uu____7962,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____7978 =
                                                     let uu____7981 =
                                                       let uu____7982 =
                                                         let uu____7990 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____7990,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7982 in
                                                     pos uu____7981 in
                                                   let uu____7996 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____7978, None,
                                                     uu____7996) in
                                                 let body =
                                                   let uu____8007 =
                                                     let uu____8010 =
                                                       let uu____8011 =
                                                         let uu____8027 =
                                                           let uu____8029 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8029] in
                                                         (arg_exp,
                                                           uu____8027) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8011 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8010 in
                                                   uu____8007 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8046 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8046
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
                                                   let uu____8052 =
                                                     let uu____8055 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8055 in
                                                   let uu____8056 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8052;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8056
                                                   } in
                                                 let impl =
                                                   let uu____8060 =
                                                     let uu____8061 =
                                                       let uu____8069 =
                                                         let uu____8071 =
                                                           let uu____8072 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8072
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8071] in
                                                       ((false, [lb]),
                                                         uu____8069, quals1,
                                                         []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8061 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8060;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1
                                                   } in
                                                 (let uu____8088 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8088
                                                  then
                                                    let uu____8089 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8089
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7836 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____8120) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8125 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8125 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8138 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8138 with
                    | (formals,uu____8148) ->
                        let uu____8159 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8172 =
                                   let uu____8173 =
                                     let uu____8174 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8174 in
                                   FStar_Ident.lid_equals typ_lid uu____8173 in
                                 if uu____8172
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8184,uvs',tps,typ0,uu____8188,constrs,uu____8190)
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
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____8159 with
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
                                      FStar_All.pipe_right quals
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
                                      FStar_Util.find_map quals
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