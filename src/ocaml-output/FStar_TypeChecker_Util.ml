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
  fun uu___100_64  ->
    match uu___100_64 with
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
                     let uu___120_181 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u in
                         (reason, env, uu____197, t, k, r) in
                       [uu____190] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___120_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___120_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___120_181.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___121_393 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_393.FStar_Syntax_Syntax.index);
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
                     let uu___122_820 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_820.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_820.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____821 =
                     let uu____824 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____824 t in
                   (match uu____821 with
                    | (e,u) ->
                        let p2 =
                          let uu___123_839 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___123_839.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___123_839.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____846 = FStar_Syntax_Util.type_u () in
              (match uu____846 with
               | (t,uu____859) ->
                   let x1 =
                     let uu___124_861 = x in
                     let uu____862 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___124_861.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___124_861.FStar_Syntax_Syntax.index);
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
                     let uu___125_899 = x in
                     let uu____900 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___125_899.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___125_899.FStar_Syntax_Syntax.index);
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
                     (let uu___126_1252 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___126_1252.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___126_1252.FStar_Syntax_Syntax.p)
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
                        let uu___127_1670 = p1 in
                        let uu____1673 =
                          let uu____1674 =
                            let uu____1682 = aux f pats1 in (fv, uu____1682) in
                          FStar_Syntax_Syntax.Pat_cons uu____1674 in
                        {
                          FStar_Syntax_Syntax.v = uu____1673;
                          FStar_Syntax_Syntax.ty =
                            (uu___127_1670.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___127_1670.FStar_Syntax_Syntax.p)
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
                          (let uu___128_1960 = p1 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___128_1960.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___128_1960.FStar_Syntax_Syntax.p)
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
                  let uu___129_2087 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___129_2087.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___129_2087.FStar_Syntax_Syntax.index);
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
                  let uu___130_2098 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___130_2098.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___130_2098.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2100),uu____2101) ->
              let s = force_sort e1 in
              let x1 =
                let uu___131_2110 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___131_2110.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___131_2110.FStar_Syntax_Syntax.index);
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
      let uu___132_2914 = lc in
      let uu____2915 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___132_2914.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2915;
        FStar_Syntax_Syntax.cflags =
          (uu___132_2914.FStar_Syntax_Syntax.cflags);
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
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2952 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2952
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2954 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2954 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2960 =
                        let uu____2961 =
                          let uu____2962 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2963 =
                            let uu____2964 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2965 =
                              let uu____2967 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2967] in
                            uu____2964 :: uu____2965 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2962 uu____2963 in
                        uu____2961 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2960) in
             (mk_comp m) u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2973 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2973
         then
           let uu____2974 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2975 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2976 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2974
             uu____2975 uu____2976
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
          fun uu____2993  ->
            match uu____2993 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3003 =
                    FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                  if uu____3003
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3006 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3008 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3009 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3006 uu____3008 bstr uu____3009
                  else ());
                 (let bind_it uu____3014 =
                    let uu____3015 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3015
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3025 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Extreme in
                        if uu____3025
                        then
                          let uu____3026 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3028 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3029 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3030 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3031 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3026 uu____3028 uu____3029 uu____3030
                            uu____3031
                        else ());
                       (let try_simplify uu____3039 =
                          let aux uu____3048 =
                            let uu____3049 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3049
                            then
                              match b with
                              | None  -> Some (c2, "trivial no binder")
                              | Some uu____3066 ->
                                  let uu____3067 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3067
                                   then Some (c2, "trivial ml")
                                   else None)
                            else
                              (let uu____3085 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3085
                               then Some (c2, "both ml")
                               else None) in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3118 =
                                  let uu____3121 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3121, reason) in
                                Some uu____3118
                            | uu____3124 -> aux () in
                          let uu____3129 =
                            (FStar_Syntax_Util.is_total_comp c1) &&
                              (FStar_Syntax_Util.is_total_comp c2) in
                          if uu____3129
                          then subst_c2 "both total"
                          else
                            (let uu____3134 =
                               (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                 (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                             if uu____3134
                             then
                               let uu____3138 =
                                 let uu____3141 =
                                   FStar_Syntax_Syntax.mk_GTotal
                                     (FStar_Syntax_Util.comp_result c2) in
                                 (uu____3141, "both gtot") in
                               Some uu____3138
                             else
                               (match (e1opt, b) with
                                | (Some e,Some x) ->
                                    let uu____3154 =
                                      (FStar_Syntax_Util.is_total_comp c1) &&
                                        (let uu____3155 =
                                           FStar_Syntax_Syntax.is_null_bv x in
                                         Prims.op_Negation uu____3155) in
                                    if uu____3154
                                    then subst_c2 "substituted e"
                                    else aux ()
                                | uu____3160 -> aux ())) in
                        let uu____3165 = try_simplify () in
                        match uu____3165 with
                        | Some (c,reason) -> c
                        | None  ->
                            let uu____3175 = lift_and_destruct env c1 c2 in
                            (match uu____3175 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3209 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3209]
                                   | Some x ->
                                       let uu____3211 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3211] in
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
                                   let uu____3238 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3239 =
                                     let uu____3241 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3242 =
                                       let uu____3244 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3245 =
                                         let uu____3247 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3248 =
                                           let uu____3250 =
                                             let uu____3251 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3251 in
                                           [uu____3250] in
                                         uu____3247 :: uu____3248 in
                                       uu____3244 :: uu____3245 in
                                     uu____3241 :: uu____3242 in
                                   uu____3238 :: uu____3239 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3256 =
                                     let uu____3257 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3257
                                       wp_args in
                                   uu____3256 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3306 =
                let uu____3307 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3307 in
              if uu____3306
              then f
              else (let uu____3309 = reason1 () in label uu____3309 r f)
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
            let uu___133_3320 = g in
            let uu____3321 =
              let uu____3322 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3322 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3321;
              FStar_TypeChecker_Env.deferred =
                (uu___133_3320.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_3320.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_3320.FStar_TypeChecker_Env.implicits)
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
      | uu____3334 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3351 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3355 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3355
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3362 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3362
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3367 = destruct_comp c1 in
                    match uu____3367 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3380 =
                            let uu____3381 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3382 =
                              let uu____3383 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3384 =
                                let uu____3386 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3387 =
                                  let uu____3389 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3389] in
                                uu____3386 :: uu____3387 in
                              uu____3383 :: uu____3384 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3381
                              uu____3382 in
                          uu____3380 None wp.FStar_Syntax_Syntax.pos in
                        (mk_comp md) u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___134_3394 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___134_3394.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___134_3394.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___134_3394.FStar_Syntax_Syntax.cflags);
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
            let uu____3421 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3421
            then (lc, g0)
            else
              ((let uu____3426 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3426
                then
                  let uu____3427 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3428 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3427 uu____3428
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___101_3434  ->
                          match uu___101_3434 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3436 -> [])) in
                let strengthen uu____3442 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3450 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3450 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3457 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3458 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3458) in
                           if uu____3457
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3465 =
                                 let uu____3466 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3466 in
                               FStar_Syntax_Util.comp_set_flags uu____3465
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3471 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3471
                           then
                             let uu____3472 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3473 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3472 uu____3473
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3476 = destruct_comp c2 in
                           match uu____3476 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3489 =
                                   let uu____3490 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3491 =
                                     let uu____3492 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3493 =
                                       let uu____3495 =
                                         let uu____3496 =
                                           let uu____3497 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3497 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3496 in
                                       let uu____3498 =
                                         let uu____3500 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3500] in
                                       uu____3495 :: uu____3498 in
                                     uu____3492 :: uu____3493 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3490
                                     uu____3491 in
                                 uu____3489 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3506 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3506
                                 then
                                   let uu____3507 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3507
                                 else ());
                                (let c21 =
                                   (mk_comp md) u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3510 =
                  let uu___135_3511 = lc in
                  let uu____3512 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3513 =
                    let uu____3515 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3516 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3516) in
                    if uu____3515 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3512;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___135_3511.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3513;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3510,
                  (let uu___136_3519 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___136_3519.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___136_3519.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___136_3519.FStar_TypeChecker_Env.implicits)
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
        let uu____3534 =
          let uu____3537 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3538 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3537, uu____3538) in
        match uu____3534 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3547 =
                let uu____3548 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3549 =
                  let uu____3550 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3551 =
                    let uu____3553 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3553] in
                  uu____3550 :: uu____3551 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3548 uu____3549 in
              uu____3547 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3561 =
                let uu____3562 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3563 =
                  let uu____3564 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3565 =
                    let uu____3567 =
                      let uu____3568 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3568 in
                    let uu____3569 =
                      let uu____3571 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3571] in
                    uu____3567 :: uu____3569 in
                  uu____3564 :: uu____3565 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3562 uu____3563 in
              uu____3561 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3579 =
                let uu____3580 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3581 =
                  let uu____3582 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3583 =
                    let uu____3585 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3586 =
                      let uu____3588 =
                        let uu____3589 =
                          let uu____3590 =
                            let uu____3591 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3591] in
                          FStar_Syntax_Util.abs uu____3590 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3589 in
                      [uu____3588] in
                    uu____3585 :: uu____3586 in
                  uu____3582 :: uu____3583 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3580 uu____3581 in
              uu____3579 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              (mk_comp md_pure) u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3607 = FStar_TypeChecker_Env.get_range env in
              bind uu____3607 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3625 =
            let uu____3626 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3626
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3629 =
                 let uu____3642 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3643 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3642 uu____3643 in
               match uu____3629 with
               | ((md,uu____3645,uu____3646),(u_res_t,res_t,wp_then),
                  (uu____3650,uu____3651,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3680 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3681 =
                       let uu____3682 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3683 =
                         let uu____3684 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3685 =
                           let uu____3687 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3688 =
                             let uu____3690 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3691 =
                               let uu____3693 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3693] in
                             uu____3690 :: uu____3691 in
                           uu____3687 :: uu____3688 in
                         uu____3684 :: uu____3685 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3682 uu____3683 in
                     uu____3681 None uu____3680 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3701 =
                     let uu____3702 = FStar_Options.split_cases () in
                     uu____3702 > (Prims.parse_int "0") in
                   if uu____3701
                   then
                     let comp = (mk_comp md) u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3708 =
                          let uu____3709 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3710 =
                            let uu____3711 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3712 =
                              let uu____3714 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3714] in
                            uu____3711 :: uu____3712 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3709 uu____3710 in
                        uu____3708 None wp.FStar_Syntax_Syntax.pos in
                      (mk_comp md) u_res_t res_t wp1 [])) in
          let uu____3719 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3719;
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
      let uu____3726 =
        let uu____3727 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3727 in
      FStar_Syntax_Syntax.fvar uu____3726 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3747  ->
                 match uu____3747 with
                 | (uu____3750,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3755 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3757 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3757
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3777 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3778 =
                 let uu____3779 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3780 =
                   let uu____3781 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3782 =
                     let uu____3784 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3785 =
                       let uu____3787 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3788 =
                         let uu____3790 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3790] in
                       uu____3787 :: uu____3788 in
                     uu____3784 :: uu____3785 in
                   uu____3781 :: uu____3782 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3779 uu____3780 in
               uu____3778 None uu____3777 in
             let default_case =
               let post_k =
                 let uu____3799 =
                   let uu____3803 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3803] in
                 let uu____3804 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3799 uu____3804 in
               let kwp =
                 let uu____3810 =
                   let uu____3814 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3814] in
                 let uu____3815 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3810 uu____3815 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3820 =
                   let uu____3821 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3821] in
                 let uu____3822 =
                   let uu____3823 =
                     let uu____3826 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3826 in
                   let uu____3827 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3823 uu____3827 in
                 FStar_Syntax_Util.abs uu____3820 uu____3822
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
                 (fun uu____3841  ->
                    fun celse  ->
                      match uu____3841 with
                      | (g,cthen) ->
                          let uu____3847 =
                            let uu____3860 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3860 celse in
                          (match uu____3847 with
                           | ((md,uu____3862,uu____3863),(uu____3864,uu____3865,wp_then),
                              (uu____3867,uu____3868,wp_else)) ->
                               let uu____3879 =
                                 ifthenelse md res_t g wp_then wp_else in
                               (mk_comp md) u_res_t res_t uu____3879 []))
                 lcases default_case in
             let uu____3880 =
               let uu____3881 = FStar_Options.split_cases () in
               uu____3881 > (Prims.parse_int "0") in
             if uu____3880
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3885 = destruct_comp comp1 in
                match uu____3885 with
                | (uu____3889,uu____3890,wp) ->
                    let wp1 =
                      let uu____3895 =
                        let uu____3896 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3897 =
                          let uu____3898 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3899 =
                            let uu____3901 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3901] in
                          uu____3898 :: uu____3899 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3896 uu____3897 in
                      uu____3895 None wp.FStar_Syntax_Syntax.pos in
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
        let close1 uu____3922 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3926 = FStar_Syntax_Util.is_ml_comp c in
          if uu____3926
          then c
          else
            (let uu____3930 =
               env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
             if uu____3930
             then c
             else
               (let close_wp u_res md res_t bvs1 wp0 =
                  FStar_List.fold_right
                    (fun x  ->
                       fun wp  ->
                         let bs =
                           let uu____3962 = FStar_Syntax_Syntax.mk_binder x in
                           [uu____3962] in
                         let us =
                           let uu____3965 =
                             let uu____3967 =
                               env.FStar_TypeChecker_Env.universe_of env
                                 x.FStar_Syntax_Syntax.sort in
                             [uu____3967] in
                           u_res :: uu____3965 in
                         let wp1 =
                           FStar_Syntax_Util.abs bs wp
                             (Some
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))) in
                         let uu____3978 =
                           let uu____3979 =
                             FStar_TypeChecker_Env.inst_effect_fun_with us
                               env md md.FStar_Syntax_Syntax.close_wp in
                           let uu____3980 =
                             let uu____3981 =
                               FStar_Syntax_Syntax.as_arg res_t in
                             let uu____3982 =
                               let uu____3984 =
                                 FStar_Syntax_Syntax.as_arg
                                   x.FStar_Syntax_Syntax.sort in
                               let uu____3985 =
                                 let uu____3987 =
                                   FStar_Syntax_Syntax.as_arg wp1 in
                                 [uu____3987] in
                               uu____3984 :: uu____3985 in
                             uu____3981 :: uu____3982 in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3979
                             uu____3980 in
                         uu____3978 None wp0.FStar_Syntax_Syntax.pos) bvs1
                    wp0 in
                let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                let uu____3993 = destruct_comp c1 in
                match uu____3993 with
                | (u_res_t,res_t,wp) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c1.FStar_Syntax_Syntax.effect_name in
                    let wp1 = close_wp u_res_t md res_t bvs wp in
                    (mk_comp md) u_res_t c1.FStar_Syntax_Syntax.result_typ
                      wp1 c1.FStar_Syntax_Syntax.flags)) in
        let uu___137_4004 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4004.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4004.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___137_4004.FStar_Syntax_Syntax.cflags);
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
        let refine1 uu____4019 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4023 =
            (let uu____4024 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4024) || env.FStar_TypeChecker_Env.lax in
          if uu____4023
          then c
          else
            (let uu____4028 = FStar_Syntax_Util.is_partial_return c in
             if uu____4028
             then c
             else
               (let uu____4032 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____4033 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid in
                     Prims.op_Negation uu____4033) in
                if uu____4032
                then
                  let uu____4036 =
                    let uu____4037 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                    let uu____4038 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format2 "%s: %s\n" uu____4037 uu____4038 in
                  failwith uu____4036
                else
                  (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                   let t = c1.FStar_Syntax_Syntax.result_typ in
                   let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x in
                   let ret1 =
                     let uu____4050 =
                       let uu____4053 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4053
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4050 in
                   let eq1 =
                     let uu____4057 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4057 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let c3 =
                     let uu____4062 =
                       let uu____4063 =
                         let uu____4068 =
                           bind e.FStar_Syntax_Syntax.pos env None
                             (FStar_Syntax_Util.lcomp_of_comp c2)
                             ((Some x), eq_ret) in
                         uu____4068.FStar_Syntax_Syntax.comp in
                       uu____4063 () in
                     FStar_Syntax_Util.comp_set_flags uu____4062
                       (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                       (FStar_Syntax_Util.comp_flags c2)) in
                   c3))) in
        let flags =
          let uu____4072 =
            ((let uu____4073 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4073) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4074 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4074) in
          if uu____4072
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let uu___138_4077 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___138_4077.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___138_4077.FStar_Syntax_Syntax.res_typ);
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
          let uu____4096 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4096 with
          | None  ->
              let uu____4101 =
                let uu____4102 =
                  let uu____4105 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4106 = FStar_TypeChecker_Env.get_range env in
                  (uu____4105, uu____4106) in
                FStar_Errors.Error uu____4102 in
              Prims.raise uu____4101
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
            let uu____4132 =
              let uu____4133 = FStar_Syntax_Subst.compress t2 in
              uu____4133.FStar_Syntax_Syntax.n in
            match uu____4132 with
            | FStar_Syntax_Syntax.Tm_type uu____4136 -> true
            | uu____4137 -> false in
          let uu____4138 =
            let uu____4139 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4139.FStar_Syntax_Syntax.n in
          match uu____4138 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4145 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4152 =
                  let uu____4153 =
                    let uu____4154 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4154 in
                  (None, uu____4153) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4152 in
              let e1 =
                let uu____4163 =
                  let uu____4164 =
                    let uu____4165 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4165] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4164 in
                uu____4163
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4172 -> (e, lc)
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
              (let uu____4192 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4192 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4205 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4217 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4217, false)
            else
              (let uu____4221 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4221, true)) in
          match gopt with
          | (None ,uu____4227) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___139_4230 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___139_4230.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___139_4230.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___139_4230.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4234 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4234 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_4239 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_4239.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_4239.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___140_4239.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_4242 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_4242.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_4242.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_4242.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4248 =
                     let uu____4249 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4249
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4254 =
                          let uu____4255 = FStar_Syntax_Subst.compress f1 in
                          uu____4255.FStar_Syntax_Syntax.n in
                        match uu____4254 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4260,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4262;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4263;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4264;_},uu____4265)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_4289 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_4289.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_4289.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___142_4289.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4290 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4295 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4295
                              then
                                let uu____4296 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4297 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4298 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4299 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4296 uu____4297 uu____4298 uu____4299
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4302 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4302 with
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
                                  let uu____4313 = destruct_comp ct in
                                  (match uu____4313 with
                                   | (u_t,uu____4320,uu____4321) ->
                                       let wp =
                                         let uu____4325 =
                                           let uu____4326 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4327 =
                                             let uu____4328 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4329 =
                                               let uu____4331 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4331] in
                                             uu____4328 :: uu____4329 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4326 uu____4327 in
                                         uu____4325
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4337 =
                                           (mk_comp md) u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4337 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4347 =
                                             let uu____4348 =
                                               let uu____4349 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4349] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4348 in
                                           uu____4347
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4355 =
                                         let uu____4358 =
                                           FStar_All.pipe_left
                                             (fun _0_28  -> Some _0_28)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4369 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4370 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4358
                                           uu____4369 e cret uu____4370 in
                                       (match uu____4355 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___143_4376 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___143_4376.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___143_4376.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4378 =
                                                let uu____4379 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4379 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4378
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4389 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4389
                                              then
                                                let uu____4390 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4390
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___102_4396  ->
                             match uu___102_4396 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4398 -> [])) in
                   let lc1 =
                     let uu___144_4400 = lc in
                     let uu____4401 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4401;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___145_4403 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___145_4403.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___145_4403.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___145_4403.FStar_TypeChecker_Env.implicits)
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
        let uu____4423 =
          let uu____4424 =
            let uu____4425 =
              let uu____4426 =
                let uu____4427 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4427 in
              [uu____4426] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4425 in
          uu____4424 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4423 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4436 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4436
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
                | (req,uu____4460)::(ens,uu____4462)::uu____4463 ->
                    let uu____4485 =
                      let uu____4487 = norm req in Some uu____4487 in
                    let uu____4488 =
                      let uu____4489 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4489 in
                    (uu____4485, uu____4488)
                | uu____4491 ->
                    let uu____4497 =
                      let uu____4498 =
                        let uu____4501 =
                          let uu____4502 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4502 in
                        (uu____4501, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4498 in
                    Prims.raise uu____4497)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4512)::uu____4513 ->
                    let uu____4527 =
                      let uu____4530 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left Prims.fst uu____4530 in
                    (match uu____4527 with
                     | (us_r,uu____4547) ->
                         let uu____4548 =
                           let uu____4551 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left Prims.fst uu____4551 in
                         (match uu____4548 with
                          | (us_e,uu____4568) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4571 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4571
                                  us_r in
                              let as_ens =
                                let uu____4573 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4573
                                  us_e in
                              let req =
                                let uu____4577 =
                                  let uu____4578 =
                                    let uu____4579 =
                                      let uu____4586 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4586] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4579 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4578 in
                                uu____4577
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4602 =
                                  let uu____4603 =
                                    let uu____4604 =
                                      let uu____4611 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4611] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4604 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4603 in
                                uu____4602 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4624 =
                                let uu____4626 = norm req in Some uu____4626 in
                              let uu____4627 =
                                let uu____4628 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4628 in
                              (uu____4624, uu____4627)))
                | uu____4630 -> failwith "Impossible"))
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
      (let uu____4650 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4650
       then
         let uu____4651 = FStar_Syntax_Print.term_to_string tm in
         let uu____4652 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4651 uu____4652
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
          (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg])))
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
              | x::[] -> Prims.fst x
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
                   Prims.raise uu____4924
                 else Some (n_available - n_expected) in
           let decr_inst uu___103_4951 =
             match uu___103_4951 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4970 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4970 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____5031) when
                          _0_29 = (Prims.parse_int "0") ->
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
let string_of_univs univs1 =
  let uu____5321 =
    let uu____5323 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5323
      (FStar_List.map
         (fun u  ->
            let uu____5333 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5333 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5321 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5345 = FStar_Util.set_is_empty x in
      if uu____5345
      then []
      else
        (let s =
           let uu____5350 =
             let uu____5352 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5352 in
           FStar_All.pipe_right uu____5350 FStar_Util.set_elements in
         (let uu____5357 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5357
          then
            let uu____5358 =
              let uu____5359 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5359 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5358
          else ());
         (let r =
            let uu____5367 = FStar_TypeChecker_Env.get_range env in
            Some uu____5367 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5379 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5379
                     then
                       let uu____5380 =
                         let uu____5381 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5381 in
                       let uu____5383 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5384 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5380 uu____5383 uu____5384
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
        let uu____5402 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5402 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___104_5429 =
  match uu___104_5429 with
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
        | ([],uu____5470) -> generalized_univ_names
        | (uu____5474,[]) -> explicit_univ_names
        | uu____5478 ->
            let uu____5483 =
              let uu____5484 =
                let uu____5487 =
                  let uu____5488 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5488 in
                (uu____5487, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5484 in
            Prims.raise uu____5483
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
      (let uu____5502 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5502
       then
         let uu____5503 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5503
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5509 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5509
        then
          let uu____5510 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5510
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5515 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5515))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5545 =
        let uu____5546 =
          FStar_Util.for_all
            (fun uu____5551  ->
               match uu____5551 with
               | (uu____5556,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5546 in
      if uu____5545
      then None
      else
        (let norm c =
           (let uu____5579 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5579
            then
              let uu____5580 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5580
            else ());
           (let c1 =
              let uu____5583 = FStar_TypeChecker_Env.should_verify env in
              if uu____5583
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5586 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5586
             then
               let uu____5587 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5587
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5621 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5621 FStar_Util.set_elements in
         let uu____5665 =
           let uu____5683 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5738  ->
                     match uu____5738 with
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
           FStar_All.pipe_right uu____5683 FStar_List.unzip in
         match uu____5665 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5900 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5900
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
                      (fun uu____5942  ->
                         match uu____5942 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5999  ->
                                       match uu____5999 with
                                       | (u,k) ->
                                           let uu____6019 =
                                             FStar_Unionfind.find u in
                                           (match uu____6019 with
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
                                                uu____6057 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6065 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6070 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6070 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6094 =
                                                         let uu____6096 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____6096 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6094 kres in
                                                     let t =
                                                       let uu____6099 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6100 =
                                                         let uu____6107 =
                                                           let uu____6113 =
                                                             let uu____6114 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6114 in
                                                           FStar_Util.Inl
                                                             uu____6113 in
                                                         Some uu____6107 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6099
                                                         uu____6100 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6129 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____6147) ->
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
                             (match uu____6129 with
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
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6537) in
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
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___146_6570 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___146_6570.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___146_6570.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6571 ->
                let uu___147_6572 = e2 in
                let uu____6573 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___147_6572.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6573;
                  FStar_Syntax_Syntax.pos =
                    (uu___147_6572.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___147_6572.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___148_6582 = env1 in
            let uu____6583 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___148_6582.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___148_6582.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___148_6582.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___148_6582.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___148_6582.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___148_6582.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___148_6582.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___148_6582.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___148_6582.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___148_6582.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___148_6582.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___148_6582.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___148_6582.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___148_6582.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___148_6582.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6583;
              FStar_TypeChecker_Env.is_iface =
                (uu___148_6582.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___148_6582.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___148_6582.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___148_6582.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___148_6582.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___148_6582.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___148_6582.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___148_6582.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6584 = check env2 t1 t2 in
          match uu____6584 with
          | None  ->
              let uu____6588 =
                let uu____6589 =
                  let uu____6592 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6593 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6592, uu____6593) in
                FStar_Errors.Error uu____6589 in
              Prims.raise uu____6588
          | Some g ->
              ((let uu____6598 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6598
                then
                  let uu____6599 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6599
                else ());
               (let uu____6601 = decorate e t2 in (uu____6601, g)))
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
        let uu____6625 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6625
        then
          let uu____6628 = discharge g1 in
          let uu____6629 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6628, uu____6629)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6641 =
               let uu____6642 =
                 let uu____6643 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6643 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6642
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6641
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6645 = destruct_comp c1 in
           match uu____6645 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6657 = FStar_TypeChecker_Env.get_range env in
                 let uu____6658 =
                   let uu____6659 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6660 =
                     let uu____6661 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6662 =
                       let uu____6664 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6664] in
                     uu____6661 :: uu____6662 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6659 uu____6660 in
                 uu____6658
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6657 in
               ((let uu____6670 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6670
                 then
                   let uu____6671 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6671
                 else ());
                (let g2 =
                   let uu____6674 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6674 in
                 let uu____6675 = discharge g2 in
                 let uu____6676 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6675, uu____6676))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___105_6700 =
        match uu___105_6700 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6706)::[] -> f fst1
        | uu____6719 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6724 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6724
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32) in
      let op_or_e e =
        let uu____6733 =
          let uu____6736 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6736 in
        FStar_All.pipe_right uu____6733
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_or_t t =
        let uu____6747 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6747
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let short_op_ite uu___106_6761 =
        match uu___106_6761 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6767)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6782)::[] ->
            let uu____6803 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6803
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6808 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6815 =
          let uu____6820 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6820) in
        let uu____6825 =
          let uu____6831 =
            let uu____6836 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6836) in
          let uu____6841 =
            let uu____6847 =
              let uu____6852 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6852) in
            let uu____6857 =
              let uu____6863 =
                let uu____6868 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6868) in
              let uu____6873 =
                let uu____6879 =
                  let uu____6884 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6884) in
                [uu____6879; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6863 :: uu____6873 in
            uu____6847 :: uu____6857 in
          uu____6831 :: uu____6841 in
        uu____6815 :: uu____6825 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6925 =
            FStar_Util.find_map table
              (fun uu____6931  ->
                 match uu____6931 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6944 = mk1 seen_args in Some uu____6944
                     else None) in
          (match uu____6925 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6947 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6951 =
      let uu____6952 = FStar_Syntax_Util.un_uinst l in
      uu____6952.FStar_Syntax_Syntax.n in
    match uu____6951 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6956 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6974)::uu____6975 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6981 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6985,Some (FStar_Syntax_Syntax.Implicit uu____6986))::uu____6987
          -> bs
      | uu____6996 ->
          let uu____6997 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6997 with
           | None  -> bs
           | Some t ->
               let uu____7000 =
                 let uu____7001 = FStar_Syntax_Subst.compress t in
                 uu____7001.FStar_Syntax_Syntax.n in
               (match uu____7000 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7005) ->
                    let uu____7016 =
                      FStar_Util.prefix_until
                        (fun uu___107_7035  ->
                           match uu___107_7035 with
                           | (uu____7039,Some (FStar_Syntax_Syntax.Implicit
                              uu____7040)) -> false
                           | uu____7042 -> true) bs' in
                    (match uu____7016 with
                     | None  -> bs
                     | Some ([],uu____7060,uu____7061) -> bs
                     | Some (imps,uu____7098,uu____7099) ->
                         let uu____7136 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7144  ->
                                   match uu____7144 with
                                   | (x,uu____7149) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7136
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7172  ->
                                     match uu____7172 with
                                     | (x,i) ->
                                         let uu____7183 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7183, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7189 -> bs))
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
              (let uu____7208 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____7208 e.FStar_Syntax_Syntax.pos)
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
          let uu____7234 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7234
          then e
          else
            (let uu____7236 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____7236 e.FStar_Syntax_Syntax.pos)
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
        (let uu____7266 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7266
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7268 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7268))
         else ());
        (let fv =
           let uu____7271 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7271 None in
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
         let uu____7278 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange in
         ((let uu___149_7291 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___149_7291.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___149_7291.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___149_7291.FStar_Syntax_Syntax.sigmeta)
           }), uu____7278))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___108_7301 =
        match uu___108_7301 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7302 -> false in
      let reducibility uu___109_7306 =
        match uu___109_7306 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7307 -> false in
      let assumption uu___110_7311 =
        match uu___110_7311 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7312 -> false in
      let reification uu___111_7316 =
        match uu___111_7316 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7318 -> false in
      let inferred uu___112_7322 =
        match uu___112_7322 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7327 -> false in
      let has_eq uu___113_7331 =
        match uu___113_7331 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7332 -> false in
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
        | uu____7357 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7360 =
        let uu____7361 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___114_7363  ->
                  match uu___114_7363 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7364 -> false)) in
        FStar_All.pipe_right uu____7361 Prims.op_Negation in
      if uu____7360
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7374 =
            let uu____7375 =
              let uu____7378 =
                let uu____7379 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7379 msg in
              (uu____7378, r) in
            FStar_Errors.Error uu____7375 in
          Prims.raise uu____7374 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7387 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7395 =
            let uu____7396 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7396 in
          if uu____7395 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7400),uu____7401,uu____7402) ->
              ((let uu____7413 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7413
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7416 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7416
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7420 ->
              let uu____7425 =
                let uu____7426 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7426 in
              if uu____7425 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7430 ->
              let uu____7434 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7434 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7437 ->
              let uu____7440 =
                let uu____7441 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7441 in
              if uu____7440 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7445 ->
              let uu____7446 =
                let uu____7447 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7447 in
              if uu____7446 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7451 ->
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
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7457 ->
              let uu____7464 =
                let uu____7465 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7465 in
              if uu____7464 then err'1 () else ()
          | uu____7469 -> ()))
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
                          let uu____7526 =
                            let uu____7529 =
                              let uu____7530 =
                                let uu____7535 =
                                  let uu____7536 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7536 in
                                (uu____7535, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7530 in
                            FStar_Syntax_Syntax.mk uu____7529 in
                          uu____7526 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7562  ->
                                  match uu____7562 with
                                  | (x,imp) ->
                                      let uu____7569 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7569, imp))) in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p in
                      let unrefined_arg_binder =
                        let uu____7575 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7575 in
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
                             let uu____7584 =
                               let uu____7585 =
                                 let uu____7586 =
                                   let uu____7587 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7588 =
                                     let uu____7589 =
                                       let uu____7590 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7590 in
                                     [uu____7589] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7587
                                     uu____7588 in
                                 uu____7586 None p in
                               FStar_Syntax_Util.b2t uu____7585 in
                             FStar_Syntax_Util.refine x uu____7584 in
                           let uu____7595 =
                             let uu___150_7596 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___150_7596.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___150_7596.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7595) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7606 =
                          FStar_List.map
                            (fun uu____7616  ->
                               match uu____7616 with
                               | (x,uu____7623) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7606 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7647  ->
                                match uu____7647 with
                                | (x,uu____7654) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7663 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7663)
                               ||
                               (let uu____7664 =
                                  let uu____7665 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7665.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7664) in
                           let quals =
                             let uu____7668 =
                               let uu____7670 =
                                 let uu____7672 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7672
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7675 =
                                 FStar_List.filter
                                   (fun uu___115_7677  ->
                                      match uu___115_7677 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7678 -> false) iquals in
                               FStar_List.append uu____7670 uu____7675 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7668 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7691 =
                                 let uu____7692 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7692 in
                               FStar_Syntax_Syntax.mk_Total uu____7691 in
                             let uu____7693 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7693 in
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
                           (let uu____7696 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7696
                            then
                              let uu____7697 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7697
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
                                             fun uu____7725  ->
                                               match uu____7725 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7741 =
                                                       let uu____7744 =
                                                         let uu____7745 =
                                                           let uu____7750 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7750,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7745 in
                                                       pos uu____7744 in
                                                     (uu____7741, b)
                                                   else
                                                     (let uu____7754 =
                                                        let uu____7757 =
                                                          let uu____7758 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7758 in
                                                        pos uu____7757 in
                                                      (uu____7754, b)))) in
                                   let pat_true =
                                     let uu____7770 =
                                       let uu____7773 =
                                         let uu____7774 =
                                           let uu____7782 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7782, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7774 in
                                       pos uu____7773 in
                                     (uu____7770, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7804 =
                                       let uu____7807 =
                                         let uu____7808 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7808 in
                                       pos uu____7807 in
                                     (uu____7804, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder) in
                                   let uu____7817 =
                                     let uu____7820 =
                                       let uu____7821 =
                                         let uu____7837 =
                                           let uu____7839 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7840 =
                                             let uu____7842 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7842] in
                                           uu____7839 :: uu____7840 in
                                         (arg_exp, uu____7837) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7821 in
                                     FStar_Syntax_Syntax.mk uu____7820 in
                                   uu____7817 None p) in
                              let dd =
                                let uu____7853 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7853
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
                                let uu____7865 =
                                  let uu____7868 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7868 in
                                let uu____7869 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7865;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7869
                                } in
                              let impl =
                                let uu____7873 =
                                  let uu____7874 =
                                    let uu____7880 =
                                      let uu____7882 =
                                        let uu____7883 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7883
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7882] in
                                    ((false, [lb]), uu____7880, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7874 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7873;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7898 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7898
                               then
                                 let uu____7899 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7899
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
                                fun uu____7919  ->
                                  match uu____7919 with
                                  | (a,uu____7923) ->
                                      let uu____7924 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7924 with
                                       | (field_name,uu____7928) ->
                                           let field_proj_tm =
                                             let uu____7930 =
                                               let uu____7931 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7931 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7930 inst_univs in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7947 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7956  ->
                                    match uu____7956 with
                                    | (x,uu____7961) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7963 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7963 with
                                         | (field_name,uu____7968) ->
                                             let t =
                                               let uu____7970 =
                                                 let uu____7971 =
                                                   let uu____7974 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7974 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7971 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7970 in
                                             let only_decl =
                                               ((let uu____7976 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7976)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7977 =
                                                    let uu____7978 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7978.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7977) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7988 =
                                                   FStar_List.filter
                                                     (fun uu___116_7990  ->
                                                        match uu___116_7990
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7991 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7988
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___117_7999  ->
                                                         match uu___117_7999
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____8000 ->
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
                                             ((let uu____8003 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8003
                                               then
                                                 let uu____8004 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8004
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
                                                           fun uu____8031  ->
                                                             match uu____8031
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8047
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8047,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8059
                                                                    =
                                                                    let uu____8062
                                                                    =
                                                                    let uu____8063
                                                                    =
                                                                    let uu____8068
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8068,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8063 in
                                                                    pos
                                                                    uu____8062 in
                                                                    (uu____8059,
                                                                    b))
                                                                   else
                                                                    (let uu____8072
                                                                    =
                                                                    let uu____8075
                                                                    =
                                                                    let uu____8076
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8076 in
                                                                    pos
                                                                    uu____8075 in
                                                                    (uu____8072,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8088 =
                                                     let uu____8091 =
                                                       let uu____8092 =
                                                         let uu____8100 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8100,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8092 in
                                                     pos uu____8091 in
                                                   let uu____8106 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8088, None,
                                                     uu____8106) in
                                                 let body =
                                                   let uu____8117 =
                                                     let uu____8120 =
                                                       let uu____8121 =
                                                         let uu____8137 =
                                                           let uu____8139 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8139] in
                                                         (arg_exp,
                                                           uu____8137) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8121 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8120 in
                                                   uu____8117 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8156 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8156
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
                                                   let uu____8162 =
                                                     let uu____8165 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8165 in
                                                   let uu____8166 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8162;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8166
                                                   } in
                                                 let impl =
                                                   let uu____8170 =
                                                     let uu____8171 =
                                                       let uu____8177 =
                                                         let uu____8179 =
                                                           let uu____8180 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8180
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8179] in
                                                       ((false, [lb]),
                                                         uu____8177, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8171 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8170;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8195 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8195
                                                  then
                                                    let uu____8196 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8196
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7947 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8226) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8229 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8229 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8242 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8242 with
                    | (formals,uu____8252) ->
                        let uu____8263 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8276 =
                                   let uu____8277 =
                                     let uu____8278 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8278 in
                                   FStar_Ident.lid_equals typ_lid uu____8277 in
                                 if uu____8276
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8288,uvs',tps,typ0,uu____8292,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8305 -> failwith "Impossible"
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
                        (match uu____8263 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8347 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8347 with
                              | (indices,uu____8357) ->
                                  let refine_domain =
                                    let uu____8369 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___118_8371  ->
                                              match uu___118_8371 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8372 -> true
                                              | uu____8377 -> false)) in
                                    if uu____8369
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___119_8384 =
                                      match uu___119_8384 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8386,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8393 -> None in
                                    let uu____8394 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8394 with
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
                                    let uu____8402 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8402 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8433  ->
                                               fun uu____8434  ->
                                                 match (uu____8433,
                                                         uu____8434)
                                                 with
                                                 | ((x,uu____8444),(x',uu____8446))
                                                     ->
                                                     let uu____8451 =
                                                       let uu____8456 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8456) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8451) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8457 -> []