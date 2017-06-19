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
    | uu____88 -> failwith "Impossible"
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
          let uu____107 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid in
          match uu____107 with
          | Some (uu____120::(tm,uu____122)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____162 ->
              let uu____169 = new_uvar_aux env k in
              (match uu____169 with
               | (t,u) ->
                   let g =
                     let uu___117_181 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u in
                         (reason, env, uu____197, t, k, r) in
                       [uu____190] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___117_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___117_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___117_181.FStar_TypeChecker_Env.univ_ineqs);
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
              (fun uu____250  ->
                 match uu____250 with
                 | (x,uu____254) -> FStar_Syntax_Print.uvar_to_string x)
              uu____242 in
          FStar_All.pipe_right uu____240 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____260 =
            let uu____261 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____261 in
          FStar_Errors.err r uu____260);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____270 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____270 with
    | None  ->
        let uu____275 =
          let uu____276 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____277 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____276 uu____277 in
        failwith uu____275
    | Some tk -> tk
let force_sort s =
  let uu____292 =
    let uu____295 = force_sort' s in FStar_Syntax_Syntax.mk uu____295 in
  uu____292 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____312  ->
      match uu____312 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____319;
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
                   let uu____351 =
                     let uu____352 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____352.FStar_Syntax_Syntax.n in
                   match uu____351 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____357 = FStar_Syntax_Util.type_u () in
                       (match uu____357 with
                        | (k,uu____363) ->
                            let t2 =
                              let uu____365 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____365
                                FStar_Pervasives.fst in
                            ((let uu___118_370 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_370.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_370.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____371 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____396) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____403) ->
                       ((fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____449) ->
                       let uu____472 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____496  ->
                                 fun uu____497  ->
                                   match (uu____496, uu____497) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____539 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____539 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____472 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____600 = aux must_check_ty1 scope body in
                            (match uu____600 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____617 =
                                         FStar_Options.ml_ish () in
                                       if uu____617
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____624 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____624
                                   then
                                     let uu____625 =
                                       FStar_Range.string_of_range r in
                                     let uu____626 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____627 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____625 uu____626 uu____627
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____635 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____643 =
                            let uu____646 =
                              let uu____647 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____647
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____646 in
                          (uu____643, false)) in
                 let uu____654 =
                   let uu____659 = t_binders env in aux false uu____659 e in
                 match uu____654 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____676 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____676
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____680 =
                                let uu____681 =
                                  let uu____684 =
                                    let uu____685 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____685 in
                                  (uu____684, rng) in
                                FStar_Errors.Error uu____681 in
                              raise uu____680)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____692 ->
               let uu____693 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____693 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____774) ->
              let uu____779 = FStar_Syntax_Util.type_u () in
              (match uu____779 with
               | (k,uu____792) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_795 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_795.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_795.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____796 =
                     let uu____799 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____799 t in
                   (match uu____796 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_813 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___120_813.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____819 = FStar_Syntax_Util.type_u () in
              (match uu____819 with
               | (t,uu____832) ->
                   let x1 =
                     let uu___121_834 = x in
                     let uu____835 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_834.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_834.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____835
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
              let uu____857 = FStar_Syntax_Util.type_u () in
              (match uu____857 with
               | (t,uu____870) ->
                   let x1 =
                     let uu___122_872 = x in
                     let uu____873 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_872.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_872.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____873
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
                     (fun uu____958  ->
                        fun uu____959  ->
                          match (uu____958, uu____959) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1058 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1058 with
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
                     let uu____1166 =
                       let uu____1169 =
                         let uu____1170 =
                           let uu____1175 =
                             let uu____1178 =
                               let uu____1179 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1180 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1179
                                 uu____1180 in
                             uu____1178 None p1.FStar_Syntax_Syntax.p in
                           (uu____1175,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1170 in
                       FStar_Syntax_Syntax.mk uu____1169 in
                     uu____1166 None p1.FStar_Syntax_Syntax.p in
                   let uu____1197 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1203 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1209 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1197, uu____1203, uu____1209, env2, e,
                     (let uu___123_1221 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___123_1221.FStar_Syntax_Syntax.p)
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
                  (fun uu____1272  ->
                     match uu____1272 with
                     | (p2,imp) ->
                         let uu____1283 = elaborate_pat env1 p2 in
                         (uu____1283, imp)) pats in
              let uu____1286 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1286 with
               | (uu____1290,t) ->
                   let uu____1292 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1292 with
                    | (f,uu____1302) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1369::uu____1370) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1396::uu____1397,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1433  ->
                                      match uu____1433 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1449 =
                                                   let uu____1451 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1451 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1449
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1453 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1453, true)
                                           | uu____1456 ->
                                               let uu____1458 =
                                                 let uu____1459 =
                                                   let uu____1462 =
                                                     let uu____1463 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1463 in
                                                   (uu____1462,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1459 in
                                               raise uu____1458)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1503,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1504))
                                   when p_imp ->
                                   let uu____1506 = aux formals' pats' in
                                   (p2, true) :: uu____1506
                               | (uu____1515,Some
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
                                   let uu____1521 = aux formals' pats2 in
                                   (p3, true) :: uu____1521
                               | (uu____1530,imp) ->
                                   let uu____1534 =
                                     let uu____1538 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1538) in
                                   let uu____1540 = aux formals' pats' in
                                   uu____1534 :: uu____1540) in
                        let uu___124_1548 = p1 in
                        let uu____1550 =
                          let uu____1551 =
                            let uu____1558 = aux f pats1 in (fv, uu____1558) in
                          FStar_Syntax_Syntax.Pat_cons uu____1551 in
                        {
                          FStar_Syntax_Syntax.v = uu____1550;
                          FStar_Syntax_Syntax.p =
                            (uu___124_1548.FStar_Syntax_Syntax.p)
                        }))
          | uu____1567 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1590 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1590 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1620 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1620 with
               | Some x ->
                   let uu____1633 =
                     let uu____1634 =
                       let uu____1637 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1637, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1634 in
                   raise uu____1633
               | uu____1646 -> (b, a, w, arg, p3)) in
        let uu____1651 = one_pat true env p in
        match uu____1651 with
        | (b,uu____1665,uu____1666,tm,p1) -> (b, tm, p1)
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
          | (uu____1701,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1703)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1708,FStar_Syntax_Syntax.Tm_constant uu____1709) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1713 =
                    let uu____1714 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1715 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1714 uu____1715 in
                  failwith uu____1713)
               else ();
               (let uu____1718 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1718
                then
                  let uu____1719 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1720 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1719
                    uu____1720
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_1724 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_1724.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_1724.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1728 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1728
                then
                  let uu____1729 =
                    let uu____1730 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1731 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1730 uu____1731 in
                  failwith uu____1729
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1735 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1735.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1735.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1737),uu____1738) ->
              let s = force_sort e1 in
              let x1 =
                let uu___127_1747 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___127_1747.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___127_1747.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1758 =
                  let uu____1759 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1759 in
                if uu____1758
                then
                  let uu____1760 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1760
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1772;
                FStar_Syntax_Syntax.pos = uu____1773;
                FStar_Syntax_Syntax.vars = uu____1774;_},args))
              ->
              ((let uu____1799 =
                  let uu____1800 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1800 Prims.op_Negation in
                if uu____1799
                then
                  let uu____1801 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1801
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1882)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1926) ->
                           let x =
                             let uu____1942 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____1942 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____1953) ->
                           let pat =
                             let uu____1968 = aux argpat e2 in
                             let uu____1969 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____1968, uu____1969) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1972 ->
                      let uu____1985 =
                        let uu____1986 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____1987 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1986 uu____1987 in
                      failwith uu____1985 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____1995;
                     FStar_Syntax_Syntax.pos = uu____1996;
                     FStar_Syntax_Syntax.vars = uu____1997;_},uu____1998);
                FStar_Syntax_Syntax.tk = uu____1999;
                FStar_Syntax_Syntax.pos = uu____2000;
                FStar_Syntax_Syntax.vars = uu____2001;_},args))
              ->
              ((let uu____2030 =
                  let uu____2031 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2031 Prims.op_Negation in
                if uu____2030
                then
                  let uu____2032 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2032
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2113)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2157) ->
                           let x =
                             let uu____2173 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2173 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2184) ->
                           let pat =
                             let uu____2199 = aux argpat e2 in
                             let uu____2200 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2199, uu____2200) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2203 ->
                      let uu____2216 =
                        let uu____2217 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2218 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2217 uu____2218 in
                      failwith uu____2216 in
                match_args [] args argpats))
          | uu____2223 ->
              let uu____2226 =
                let uu____2227 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2228 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2229 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2227 uu____2228 uu____2229 in
              failwith uu____2226 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let mk1 f = (FStar_Syntax_Syntax.mk f) None pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2261 =
      match uu____2261 with
      | (p,i) ->
          let uu____2271 = decorated_pattern_as_term p in
          (match uu____2271 with
           | (vars,te) ->
               let uu____2284 =
                 let uu____2287 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2287) in
               (vars, uu____2284)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2295 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2295)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2298 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2298)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2301 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2301)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2313 =
          let uu____2321 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2321 FStar_List.unzip in
        (match uu____2313 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2378 =
               let uu____2379 =
                 let uu____2380 =
                   let uu____2390 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2390, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2380 in
               mk1 uu____2379 in
             (vars1, uu____2378))
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
      | (wp,uu____2419)::[] -> wp
      | uu____2432 ->
          let uu____2438 =
            let uu____2439 =
              let uu____2440 =
                FStar_List.map
                  (fun uu____2444  ->
                     match uu____2444 with
                     | (x,uu____2448) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2440 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2439 in
          failwith uu____2438 in
    let uu____2452 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2452, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2466 = destruct_comp c in
        match uu____2466 with
        | (u,uu____2471,wp) ->
            let uu____2473 =
              let uu____2479 =
                let uu____2480 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2480 in
              [uu____2479] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2473;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2490 =
          let uu____2494 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2495 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2494 uu____2495 in
        match uu____2490 with | (m,uu____2497,uu____2498) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2508 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2508
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
        let uu____2533 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2533 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2555 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2555 with
             | (a,kwp) ->
                 let uu____2572 = destruct_comp m1 in
                 let uu____2576 = destruct_comp m2 in
                 ((md, a, kwp), uu____2572, uu____2576))
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
            let uu____2624 =
              let uu____2625 =
                let uu____2631 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2631] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2625;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2624
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
      let uu___128_2667 = lc in
      let uu____2668 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___128_2667.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2668;
        FStar_Syntax_Syntax.cflags =
          (uu___128_2667.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2671  ->
             let uu____2672 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2672)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2676 =
      let uu____2677 = FStar_Syntax_Subst.compress t in
      uu____2677.FStar_Syntax_Syntax.n in
    match uu____2676 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2680 -> true
    | uu____2688 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2700 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2700
        then c
        else
          (let uu____2702 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2702
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2732 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2732] in
                       let us =
                         let uu____2735 =
                           let uu____2737 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2737] in
                         u_res :: uu____2735 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2748 =
                         let uu____2749 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2750 =
                           let uu____2751 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2752 =
                             let uu____2754 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2755 =
                               let uu____2757 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2757] in
                             uu____2754 :: uu____2755 in
                           uu____2751 :: uu____2752 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2749 uu____2750 in
                       uu____2748 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2763 = destruct_comp c1 in
              match uu____2763 with
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
        let close1 uu____2786 =
          let uu____2787 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2787 in
        let uu___129_2788 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_2788.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_2788.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___129_2788.FStar_Syntax_Syntax.cflags);
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
          let uu____2799 =
            let uu____2800 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2800 in
          if uu____2799
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2805 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2805
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2807 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2807 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2813 =
                        let uu____2814 =
                          let uu____2815 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____2816 =
                            let uu____2817 = FStar_Syntax_Syntax.as_arg t in
                            let uu____2818 =
                              let uu____2820 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____2820] in
                            uu____2817 :: uu____2818 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2815 uu____2816 in
                        uu____2814 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2813) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____2826 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____2826
         then
           let uu____2827 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____2828 = FStar_Syntax_Print.term_to_string v1 in
           let uu____2829 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2827
             uu____2828 uu____2829
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
          fun uu____2846  ->
            match uu____2846 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____2856 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____2856
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____2859 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____2861 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____2862 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____2859 uu____2861 bstr uu____2862
                  else ());
                 (let bind_it uu____2867 =
                    let uu____2868 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____2868
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____2878 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____2878
                        then
                          let uu____2879 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____2881 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____2882 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____2883 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____2884 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____2879 uu____2881 uu____2882 uu____2883
                            uu____2884
                        else ());
                       (let try_simplify uu____2895 =
                          let aux uu____2905 =
                            let uu____2906 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____2906
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____2925 ->
                                  let uu____2926 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____2926
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____2945 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____2945
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____2981 =
                                  let uu____2984 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____2984, reason) in
                                FStar_Util.Inl uu____2981
                            | uu____2987 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3002 =
                              let uu____3003 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3003.FStar_Syntax_Syntax.n in
                            match uu____3002 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3007) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3013 -> c in
                          let uu____3014 =
                            let uu____3015 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3015 in
                          if uu____3014
                          then
                            let uu____3023 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3023
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3037 =
                                  let uu____3038 =
                                    let uu____3041 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3041) in
                                  FStar_Errors.Error uu____3038 in
                                raise uu____3037))
                          else
                            (let uu____3049 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3049
                             then subst_c2 "both total"
                             else
                               (let uu____3057 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3057
                                then
                                  let uu____3064 =
                                    let uu____3067 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3067, "both gtot") in
                                  FStar_Util.Inl uu____3064
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3083 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3084 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3084) in
                                       if uu____3083
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___130_3093 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___130_3093.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___130_3093.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3094 =
                                           let uu____3097 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3097, "c1 Tot") in
                                         FStar_Util.Inl uu____3094
                                       else aux ()
                                   | uu____3101 -> aux ()))) in
                        let uu____3106 = try_simplify () in
                        match uu____3106 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3124 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3124
                              then
                                let uu____3125 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3126 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3127 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3125 uu____3126 uu____3127
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3134 = lift_and_destruct env c1 c2 in
                            (match uu____3134 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3168 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3168]
                                   | Some x ->
                                       let uu____3170 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3170] in
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
                                   let uu____3193 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3194 =
                                     let uu____3196 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3197 =
                                       let uu____3199 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3200 =
                                         let uu____3202 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3203 =
                                           let uu____3205 =
                                             let uu____3206 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3206 in
                                           [uu____3205] in
                                         uu____3202 :: uu____3203 in
                                       uu____3199 :: uu____3200 in
                                     uu____3196 :: uu____3197 in
                                   uu____3193 :: uu____3194 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3211 =
                                     let uu____3212 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3212
                                       wp_args in
                                   uu____3211 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3256 =
                let uu____3257 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3257 in
              if uu____3256
              then f
              else (let uu____3259 = reason1 () in label uu____3259 r f)
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
            let uu___131_3270 = g in
            let uu____3271 =
              let uu____3272 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3272 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3271;
              FStar_TypeChecker_Env.deferred =
                (uu___131_3270.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_3270.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_3270.FStar_TypeChecker_Env.implicits)
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
      | uu____3282 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3299 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3303 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3303
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3310 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3310
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3315 = destruct_comp c1 in
                    match uu____3315 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3328 =
                            let uu____3329 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3330 =
                              let uu____3331 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3332 =
                                let uu____3334 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3335 =
                                  let uu____3337 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3337] in
                                uu____3334 :: uu____3335 in
                              uu____3331 :: uu____3332 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3329
                              uu____3330 in
                          uu____3328 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___132_3342 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_3342.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_3342.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_3342.FStar_Syntax_Syntax.cflags);
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
            let uu____3369 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3369
            then (lc, g0)
            else
              ((let uu____3374 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3374
                then
                  let uu____3375 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3376 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3375 uu____3376
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3382  ->
                          match uu___98_3382 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3384 -> [])) in
                let strengthen uu____3390 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3398 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3398 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3405 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3406 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3406) in
                           if uu____3405
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3413 =
                                 let uu____3414 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3414 in
                               FStar_Syntax_Util.comp_set_flags uu____3413
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3419 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3419
                           then
                             let uu____3420 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3421 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3420 uu____3421
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3424 = destruct_comp c2 in
                           match uu____3424 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3437 =
                                   let uu____3438 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3439 =
                                     let uu____3440 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3441 =
                                       let uu____3443 =
                                         let uu____3444 =
                                           let uu____3445 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3445 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3444 in
                                       let uu____3446 =
                                         let uu____3448 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3448] in
                                       uu____3443 :: uu____3446 in
                                     uu____3440 :: uu____3441 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3438
                                     uu____3439 in
                                 uu____3437 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3454 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3454
                                 then
                                   let uu____3455 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3455
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3458 =
                  let uu___133_3459 = lc in
                  let uu____3460 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3461 =
                    let uu____3463 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3464 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3464) in
                    if uu____3463 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3460;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___133_3459.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3461;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3458,
                  (let uu___134_3467 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___134_3467.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___134_3467.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___134_3467.FStar_TypeChecker_Env.implicits)
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
        let uu____3482 =
          let uu____3485 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3486 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3485, uu____3486) in
        match uu____3482 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3495 =
                let uu____3496 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3497 =
                  let uu____3498 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3499 =
                    let uu____3501 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3501] in
                  uu____3498 :: uu____3499 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3496 uu____3497 in
              uu____3495 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3509 =
                let uu____3510 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3511 =
                  let uu____3512 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3513 =
                    let uu____3515 =
                      let uu____3516 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3516 in
                    let uu____3517 =
                      let uu____3519 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3519] in
                    uu____3515 :: uu____3517 in
                  uu____3512 :: uu____3513 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3510 uu____3511 in
              uu____3509 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3527 =
                let uu____3528 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3529 =
                  let uu____3530 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3531 =
                    let uu____3533 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3534 =
                      let uu____3536 =
                        let uu____3537 =
                          let uu____3538 =
                            let uu____3539 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3539] in
                          FStar_Syntax_Util.abs uu____3538 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3537 in
                      [uu____3536] in
                    uu____3533 :: uu____3534 in
                  uu____3530 :: uu____3531 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3528 uu____3529 in
              uu____3527 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3555 = FStar_TypeChecker_Env.get_range env in
              bind uu____3555 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3573 =
            let uu____3574 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3574
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3577 =
                 let uu____3590 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3591 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3590 uu____3591 in
               match uu____3577 with
               | ((md,uu____3593,uu____3594),(u_res_t,res_t,wp_then),
                  (uu____3598,uu____3599,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3628 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3629 =
                       let uu____3630 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3631 =
                         let uu____3632 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3633 =
                           let uu____3635 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3636 =
                             let uu____3638 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3639 =
                               let uu____3641 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3641] in
                             uu____3638 :: uu____3639 in
                           uu____3635 :: uu____3636 in
                         uu____3632 :: uu____3633 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3630 uu____3631 in
                     uu____3629 None uu____3628 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3649 =
                     let uu____3650 = FStar_Options.split_cases () in
                     uu____3650 > (Prims.parse_int "0") in
                   if uu____3649
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3656 =
                          let uu____3657 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3658 =
                            let uu____3659 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3660 =
                              let uu____3662 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3662] in
                            uu____3659 :: uu____3660 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3657 uu____3658 in
                        uu____3656 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3667 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3667;
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
      let uu____3674 =
        let uu____3675 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3675 in
      FStar_Syntax_Syntax.fvar uu____3674 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3695  ->
                 match uu____3695 with
                 | (uu____3698,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3703 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3705 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3705
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3725 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3726 =
                 let uu____3727 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3728 =
                   let uu____3729 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3730 =
                     let uu____3732 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3733 =
                       let uu____3735 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3736 =
                         let uu____3738 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3738] in
                       uu____3735 :: uu____3736 in
                     uu____3732 :: uu____3733 in
                   uu____3729 :: uu____3730 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3727 uu____3728 in
               uu____3726 None uu____3725 in
             let default_case =
               let post_k =
                 let uu____3747 =
                   let uu____3751 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3751] in
                 let uu____3752 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3747 uu____3752 in
               let kwp =
                 let uu____3758 =
                   let uu____3762 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3762] in
                 let uu____3763 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3758 uu____3763 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3768 =
                   let uu____3769 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3769] in
                 let uu____3770 =
                   let uu____3771 =
                     let uu____3774 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3774 in
                   let uu____3775 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3771 uu____3775 in
                 FStar_Syntax_Util.abs uu____3768 uu____3770
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
                 (fun uu____3789  ->
                    fun celse  ->
                      match uu____3789 with
                      | (g,cthen) ->
                          let uu____3795 =
                            let uu____3808 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3808 celse in
                          (match uu____3795 with
                           | ((md,uu____3810,uu____3811),(uu____3812,uu____3813,wp_then),
                              (uu____3815,uu____3816,wp_else)) ->
                               let uu____3827 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____3827 []))
                 lcases default_case in
             let uu____3828 =
               let uu____3829 = FStar_Options.split_cases () in
               uu____3829 > (Prims.parse_int "0") in
             if uu____3828
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____3833 = destruct_comp comp1 in
                match uu____3833 with
                | (uu____3837,uu____3838,wp) ->
                    let wp1 =
                      let uu____3843 =
                        let uu____3844 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____3845 =
                          let uu____3846 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____3847 =
                            let uu____3849 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____3849] in
                          uu____3846 :: uu____3847 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3844 uu____3845 in
                      uu____3843 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____3865 =
            ((let uu____3866 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____3866) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3867 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____3867) in
          if uu____3865
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____3875 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3879 =
            (let uu____3880 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____3880) || env.FStar_TypeChecker_Env.lax in
          if uu____3879
          then c
          else
            (let uu____3884 = FStar_Syntax_Util.is_partial_return c in
             if uu____3884
             then c
             else
               (let uu____3888 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____3888
                then
                  let uu____3891 =
                    let uu____3892 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____3892 in
                  (if uu____3891
                   then
                     let uu____3895 =
                       let uu____3896 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____3897 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____3896 uu____3897 in
                     failwith uu____3895
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____3902 =
                        let uu____3903 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____3903 in
                      if uu____3902
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___135_3908 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___135_3908.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___135_3908.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___135_3908.FStar_Syntax_Syntax.effect_args);
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
                     let uu____3919 =
                       let uu____3922 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____3922
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____3919 in
                   let eq1 =
                     let uu____3926 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____3926 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____3928 =
                     let uu____3929 =
                       let uu____3934 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____3934.FStar_Syntax_Syntax.comp in
                     uu____3929 () in
                   FStar_Syntax_Util.comp_set_flags uu____3928 flags))) in
        let uu___136_3936 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_3936.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_3936.FStar_Syntax_Syntax.res_typ);
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
          let uu____3955 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____3955 with
          | None  ->
              let uu____3960 =
                let uu____3961 =
                  let uu____3964 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____3965 = FStar_TypeChecker_Env.get_range env in
                  (uu____3964, uu____3965) in
                FStar_Errors.Error uu____3961 in
              raise uu____3960
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
            let uu____3991 =
              let uu____3992 = FStar_Syntax_Subst.compress t2 in
              uu____3992.FStar_Syntax_Syntax.n in
            match uu____3991 with
            | FStar_Syntax_Syntax.Tm_type uu____3995 -> true
            | uu____3996 -> false in
          let uu____3997 =
            let uu____3998 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____3998.FStar_Syntax_Syntax.n in
          match uu____3997 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4004 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4011 =
                  let uu____4012 =
                    let uu____4013 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4013 in
                  (None, uu____4012) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4011 in
              let e1 =
                let uu____4022 =
                  let uu____4023 =
                    let uu____4024 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4024] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4023 in
                uu____4022
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4031 -> (e, lc)
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
              (let uu____4051 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4051 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4064 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4076 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4076, false)
            else
              (let uu____4080 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4080, true)) in
          match gopt with
          | (None ,uu____4086) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___137_4089 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___137_4089.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___137_4089.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___137_4089.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4093 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4093 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___138_4098 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___138_4098.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___138_4098.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___138_4098.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4101 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4101.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4101.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4101.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4107 =
                     let uu____4108 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4108
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4113 =
                          let uu____4114 = FStar_Syntax_Subst.compress f1 in
                          uu____4114.FStar_Syntax_Syntax.n in
                        match uu____4113 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4119,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4121;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4122;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4123;_},uu____4124)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4148 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___140_4148.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___140_4148.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___140_4148.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4149 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4154 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4154
                              then
                                let uu____4155 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4156 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4157 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4158 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4155 uu____4156 uu____4157 uu____4158
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4161 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4161 with
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
                                  let uu____4172 = destruct_comp ct in
                                  (match uu____4172 with
                                   | (u_t,uu____4179,uu____4180) ->
                                       let wp =
                                         let uu____4184 =
                                           let uu____4185 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4186 =
                                             let uu____4187 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4188 =
                                               let uu____4190 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4190] in
                                             uu____4187 :: uu____4188 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4185 uu____4186 in
                                         uu____4184
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4196 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4196 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4206 =
                                             let uu____4207 =
                                               let uu____4208 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4208] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4207 in
                                           uu____4206
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4214 =
                                         let uu____4217 =
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4228 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4229 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4217
                                           uu____4228 e cret uu____4229 in
                                       (match uu____4214 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___141_4235 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___141_4235.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___141_4235.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4237 =
                                                let uu____4238 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4238 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4237
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4248 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4248
                                              then
                                                let uu____4249 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4249
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4255  ->
                             match uu___99_4255 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4257 -> [])) in
                   let lc1 =
                     let uu___142_4259 = lc in
                     let uu____4260 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4260;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___143_4262 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4262.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4262.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4262.FStar_TypeChecker_Env.implicits)
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
        let uu____4282 =
          let uu____4283 =
            let uu____4284 =
              let uu____4285 =
                let uu____4286 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4286 in
              [uu____4285] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4284 in
          uu____4283 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4282 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4295 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4295
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4306 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4315 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4332)::(ens,uu____4334)::uu____4335 ->
                    let uu____4357 =
                      let uu____4359 = norm req in Some uu____4359 in
                    let uu____4360 =
                      let uu____4361 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4361 in
                    (uu____4357, uu____4360)
                | uu____4363 ->
                    let uu____4369 =
                      let uu____4370 =
                        let uu____4373 =
                          let uu____4374 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4374 in
                        (uu____4373, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4370 in
                    raise uu____4369)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4384)::uu____4385 ->
                    let uu____4399 =
                      let uu____4402 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4402 in
                    (match uu____4399 with
                     | (us_r,uu____4419) ->
                         let uu____4420 =
                           let uu____4423 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4423 in
                         (match uu____4420 with
                          | (us_e,uu____4440) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4443 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4443
                                  us_r in
                              let as_ens =
                                let uu____4445 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4445
                                  us_e in
                              let req =
                                let uu____4449 =
                                  let uu____4450 =
                                    let uu____4451 =
                                      let uu____4458 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4458] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4451 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4450 in
                                uu____4449
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4474 =
                                  let uu____4475 =
                                    let uu____4476 =
                                      let uu____4483 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4483] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4476 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4475 in
                                uu____4474 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4496 =
                                let uu____4498 = norm req in Some uu____4498 in
                              let uu____4499 =
                                let uu____4500 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4500 in
                              (uu____4496, uu____4499)))
                | uu____4502 -> failwith "Impossible"))
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
      (let uu____4522 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4522
       then
         let uu____4523 = FStar_Syntax_Print.term_to_string tm in
         let uu____4524 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4523 uu____4524
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
        (let uu____4545 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4545
         then
           let uu____4546 = FStar_Syntax_Print.term_to_string tm in
           let uu____4547 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4546
             uu____4547
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4552 =
      let uu____4553 =
        let uu____4554 = FStar_Syntax_Subst.compress t in
        uu____4554.FStar_Syntax_Syntax.n in
      match uu____4553 with
      | FStar_Syntax_Syntax.Tm_app uu____4557 -> false
      | uu____4567 -> true in
    if uu____4552
    then t
    else
      (let uu____4569 = FStar_Syntax_Util.head_and_args t in
       match uu____4569 with
       | (head1,args) ->
           let uu____4595 =
             let uu____4596 =
               let uu____4597 = FStar_Syntax_Subst.compress head1 in
               uu____4597.FStar_Syntax_Syntax.n in
             match uu____4596 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4600 -> false in
           if uu____4595
           then
             (match args with
              | x::[] -> fst x
              | uu____4616 ->
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
             let uu____4644 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4644 with
             | (formals,uu____4653) ->
                 let n_implicits =
                   let uu____4665 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4702  ->
                             match uu____4702 with
                             | (uu____4706,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4665 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4778 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4778 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4792 =
                     let uu____4793 =
                       let uu____4796 =
                         let uu____4797 = FStar_Util.string_of_int n_expected in
                         let uu____4801 = FStar_Syntax_Print.term_to_string e in
                         let uu____4802 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4797 uu____4801 uu____4802 in
                       let uu____4806 = FStar_TypeChecker_Env.get_range env in
                       (uu____4796, uu____4806) in
                     FStar_Errors.Error uu____4793 in
                   raise uu____4792
                 else Some (n_available - n_expected) in
           let decr_inst uu___100_4819 =
             match uu___100_4819 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4838 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____4838 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_30,uu____4899) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4921,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____4940 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____4940 with
                           | (v1,uu____4961,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____4971 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____4971 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5020 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5020)))
                      | (uu____5034,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5058 =
                      let uu____5072 = inst_n_binders t in
                      aux [] uu____5072 bs1 in
                    (match uu____5058 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5110) -> (e, torig, guard)
                          | (uu____5126,[]) when
                              let uu____5142 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5142 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5143 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5162 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5177 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5183 =
      let uu____5185 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5185
        (FStar_List.map
           (fun u  ->
              let uu____5190 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5190 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5183 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5202 = FStar_Util.set_is_empty x in
      if uu____5202
      then []
      else
        (let s =
           let uu____5207 =
             let uu____5209 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5209 in
           FStar_All.pipe_right uu____5207 FStar_Util.set_elements in
         (let uu____5214 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5214
          then
            let uu____5215 =
              let uu____5216 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5216 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5215
          else ());
         (let r =
            let uu____5221 = FStar_TypeChecker_Env.get_range env in
            Some uu____5221 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5229 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5229
                     then
                       let uu____5230 =
                         let uu____5231 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5231 in
                       let uu____5232 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5233 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5230 uu____5232 uu____5233
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
        let uu____5250 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5250 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5277 =
  match uu___101_5277 with
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
        | ([],uu____5318) -> generalized_univ_names
        | (uu____5322,[]) -> explicit_univ_names
        | uu____5326 ->
            let uu____5331 =
              let uu____5332 =
                let uu____5335 =
                  let uu____5336 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5336 in
                (uu____5335, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5332 in
            raise uu____5331
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
      (let uu____5350 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5350
       then
         let uu____5351 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5351
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5356 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5356
        then
          let uu____5357 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5357
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____5363 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5363))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5393 =
        let uu____5394 =
          FStar_Util.for_all
            (fun uu____5399  ->
               match uu____5399 with
               | (uu____5404,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5394 in
      if uu____5393
      then None
      else
        (let norm c =
           (let uu____5427 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5427
            then
              let uu____5428 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5428
            else ());
           (let c1 =
              let uu____5431 = FStar_TypeChecker_Env.should_verify env in
              if uu____5431
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5434 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5434
             then
               let uu____5435 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5435
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5475 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5475 FStar_Util.set_elements in
         let uu____5529 =
           let uu____5549 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5610  ->
                     match uu____5610 with
                     | (e,c) ->
                         let t =
                           FStar_All.pipe_right
                             (FStar_Syntax_Util.comp_result c)
                             FStar_Syntax_Subst.compress in
                         let c1 = norm c in
                         let t1 = FStar_Syntax_Util.comp_result c1 in
                         let univs1 = FStar_Syntax_Free.univs t1 in
                         let uvt = FStar_Syntax_Free.uvars t1 in
                         ((let uu____5652 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Gen") in
                           if uu____5652
                           then
                             let uu____5653 =
                               let uu____5654 =
                                 let uu____5656 =
                                   FStar_Util.set_elements univs1 in
                                 FStar_All.pipe_right uu____5656
                                   (FStar_List.map
                                      (fun u  ->
                                         FStar_Syntax_Print.univ_to_string
                                           (FStar_Syntax_Syntax.U_unif u))) in
                               FStar_All.pipe_right uu____5654
                                 (FStar_String.concat ", ") in
                             let uu____5670 =
                               let uu____5671 =
                                 let uu____5673 = FStar_Util.set_elements uvt in
                                 FStar_All.pipe_right uu____5673
                                   (FStar_List.map
                                      (fun uu____5685  ->
                                         match uu____5685 with
                                         | (u,t2) ->
                                             let uu____5690 =
                                               FStar_Syntax_Print.uvar_to_string
                                                 u in
                                             let uu____5691 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2 in
                                             FStar_Util.format2 "(%s : %s)"
                                               uu____5690 uu____5691)) in
                               FStar_All.pipe_right uu____5671
                                 (FStar_String.concat ", ") in
                             FStar_Util.print2
                               "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                               uu____5653 uu____5670
                           else ());
                          (let univs2 =
                             let uu____5696 = FStar_Util.set_elements uvt in
                             FStar_List.fold_left
                               (fun univs2  ->
                                  fun uu____5706  ->
                                    match uu____5706 with
                                    | (uu____5711,t2) ->
                                        let uu____5713 =
                                          FStar_Syntax_Free.univs t2 in
                                        FStar_Util.set_union univs2
                                          uu____5713) univs1 uu____5696 in
                           let uvs = gen_uvars uvt in
                           (let uu____5728 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Gen") in
                            if uu____5728
                            then
                              let uu____5729 =
                                let uu____5730 =
                                  let uu____5732 =
                                    FStar_Util.set_elements univs2 in
                                  FStar_All.pipe_right uu____5732
                                    (FStar_List.map
                                       (fun u  ->
                                          FStar_Syntax_Print.univ_to_string
                                            (FStar_Syntax_Syntax.U_unif u))) in
                                FStar_All.pipe_right uu____5730
                                  (FStar_String.concat ", ") in
                              let uu____5746 =
                                let uu____5747 =
                                  FStar_All.pipe_right uvs
                                    (FStar_List.map
                                       (fun uu____5763  ->
                                          match uu____5763 with
                                          | (u,t2) ->
                                              let uu____5768 =
                                                FStar_Syntax_Print.uvar_to_string
                                                  u in
                                              let uu____5769 =
                                                FStar_Syntax_Print.term_to_string
                                                  t2 in
                                              FStar_Util.format2 "(%s : %s)"
                                                uu____5768 uu____5769)) in
                                FStar_All.pipe_right uu____5747
                                  (FStar_String.concat ", ") in
                              FStar_Util.print2
                                "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                                uu____5729 uu____5746
                            else ());
                           (univs2, (uvs, e, c1)))))) in
           FStar_All.pipe_right uu____5549 FStar_List.unzip in
         match uu____5529 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5894 = FStar_List.hd univs1 in
               let uu____5897 = FStar_List.tl univs1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun u  ->
                      let uu____5907 =
                        (FStar_Util.set_is_subset_of out u) &&
                          (FStar_Util.set_is_subset_of u out) in
                      if uu____5907
                      then out
                      else
                        (let uu____5910 =
                           let uu____5911 =
                             let uu____5914 =
                               FStar_TypeChecker_Env.get_range env in
                             ("Generalizing the types of these mutually recursive definitions requires an incompatible set of universes",
                               uu____5914) in
                           FStar_Errors.Error uu____5911 in
                         raise uu____5910)) uu____5894 uu____5897 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5919 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5919
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
                      (fun uu____5959  ->
                         match uu____5959 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5996  ->
                                       match uu____5996 with
                                       | (u,k) ->
                                           let uu____6004 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6004 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6010;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6011;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6012;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6018,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6020;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6021;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6022;_},uu____6023);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6024;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6025;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6026;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6054 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6058 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6061 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6061 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6085 =
                                                         let uu____6087 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              Some _0_31)
                                                           uu____6087 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6085 kres in
                                                     let t =
                                                       let uu____6090 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6091 =
                                                         let uu____6098 =
                                                           let uu____6104 =
                                                             let uu____6105 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6105 in
                                                           FStar_Util.Inl
                                                             uu____6104 in
                                                         Some uu____6098 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6090
                                                         uu____6091 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6118 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm;
                                       FStar_TypeChecker_Normalize.CompressUvars]
                                       env c in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (e1, c1)
                               | uu____6138 ->
                                   let uu____6146 = (e, c) in
                                   (match uu____6146 with
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
                                          let uu____6158 =
                                            let uu____6159 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6159.FStar_Syntax_Syntax.n in
                                          match uu____6158 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6176 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6176 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6186 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6196 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6196)) in
                             (match uu____6118 with
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
      (let uu____6234 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6234
       then
         let uu____6235 =
           let uu____6236 =
             FStar_List.map
               (fun uu____6241  ->
                  match uu____6241 with
                  | (lb,uu____6246,uu____6247) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6236 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6235
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6257  ->
              match uu____6257 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6272 =
           let uu____6279 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6295  ->
                     match uu____6295 with | (uu____6301,e,c) -> (e, c))) in
           gen env uu____6279 in
         match uu____6272 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6333  ->
                     match uu____6333 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6377  ->
                  fun uu____6378  ->
                    match (uu____6377, uu____6378) with
                    | ((l,uu____6411,uu____6412),(us,e,c)) ->
                        ((let uu____6438 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6438
                          then
                            let uu____6439 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6440 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6441 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6442 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6439 uu____6440 uu____6441 uu____6442
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6461  ->
              match uu____6461 with
              | (l,generalized_univs,t,c) ->
                  let uu____6479 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6479, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6512 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6512 with
               | None  -> None
               | Some f ->
                   let uu____6516 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____6516) in
          let is_var e1 =
            let uu____6522 =
              let uu____6523 = FStar_Syntax_Subst.compress e1 in
              uu____6523.FStar_Syntax_Syntax.n in
            match uu____6522 with
            | FStar_Syntax_Syntax.Tm_name uu____6526 -> true
            | uu____6527 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___144_6545 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_6545.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_6545.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6546 ->
                let uu___145_6547 = e2 in
                let uu____6548 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6547.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6548;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6547.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6547.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___146_6557 = env1 in
            let uu____6558 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6557.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6557.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6557.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6557.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6557.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6557.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6557.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6557.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6557.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6557.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6557.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6557.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6557.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6557.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6557.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6558;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6557.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6557.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6557.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6557.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6557.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6557.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6557.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6557.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6559 = check env2 t1 t2 in
          match uu____6559 with
          | None  ->
              let uu____6563 =
                let uu____6564 =
                  let uu____6567 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6568 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6567, uu____6568) in
                FStar_Errors.Error uu____6564 in
              raise uu____6563
          | Some g ->
              ((let uu____6573 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6573
                then
                  let uu____6574 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6574
                else ());
               (let uu____6576 = decorate e t2 in (uu____6576, g)))
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
        let uu____6600 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6600
        then
          let uu____6603 = discharge g1 in
          let uu____6604 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6603, uu____6604)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6616 =
               let uu____6617 =
                 let uu____6618 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6618 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6617
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6616
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6620 = destruct_comp c1 in
           match uu____6620 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6632 = FStar_TypeChecker_Env.get_range env in
                 let uu____6633 =
                   let uu____6634 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6635 =
                     let uu____6636 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6637 =
                       let uu____6639 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6639] in
                     uu____6636 :: uu____6637 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6634 uu____6635 in
                 uu____6633
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6632 in
               ((let uu____6645 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6645
                 then
                   let uu____6646 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6646
                 else ());
                (let g2 =
                   let uu____6649 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6649 in
                 let uu____6650 = discharge g2 in
                 let uu____6651 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6650, uu____6651))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6675 =
        match uu___102_6675 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6681)::[] -> f fst1
        | uu____6694 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6699 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6699
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____6708 =
          let uu____6711 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6711 in
        FStar_All.pipe_right uu____6708
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____6722 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6722
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_6736 =
        match uu___103_6736 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6742)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6757)::[] ->
            let uu____6778 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6778
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____6783 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6790 =
          let uu____6795 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6795) in
        let uu____6800 =
          let uu____6806 =
            let uu____6811 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6811) in
          let uu____6816 =
            let uu____6822 =
              let uu____6827 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6827) in
            let uu____6832 =
              let uu____6838 =
                let uu____6843 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6843) in
              let uu____6848 =
                let uu____6854 =
                  let uu____6859 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6859) in
                [uu____6854; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6838 :: uu____6848 in
            uu____6822 :: uu____6832 in
          uu____6806 :: uu____6816 in
        uu____6790 :: uu____6800 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6896 =
            FStar_Util.find_map table
              (fun uu____6902  ->
                 match uu____6902 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6915 = mk1 seen_args in Some uu____6915
                     else None) in
          (match uu____6896 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6918 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6922 =
      let uu____6923 = FStar_Syntax_Util.un_uinst l in
      uu____6923.FStar_Syntax_Syntax.n in
    match uu____6922 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6927 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6945)::uu____6946 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6952 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____6956,Some (FStar_Syntax_Syntax.Implicit uu____6957))::uu____6958
          -> bs
      | uu____6967 ->
          let uu____6968 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____6968 with
           | None  -> bs
           | Some t ->
               let uu____6971 =
                 let uu____6972 = FStar_Syntax_Subst.compress t in
                 uu____6972.FStar_Syntax_Syntax.n in
               (match uu____6971 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6976) ->
                    let uu____6987 =
                      FStar_Util.prefix_until
                        (fun uu___104_7006  ->
                           match uu___104_7006 with
                           | (uu____7010,Some (FStar_Syntax_Syntax.Implicit
                              uu____7011)) -> false
                           | uu____7013 -> true) bs' in
                    (match uu____6987 with
                     | None  -> bs
                     | Some ([],uu____7031,uu____7032) -> bs
                     | Some (imps,uu____7069,uu____7070) ->
                         let uu____7107 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7115  ->
                                   match uu____7115 with
                                   | (x,uu____7120) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7107
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7143  ->
                                     match uu____7143 with
                                     | (x,i) ->
                                         let uu____7154 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7154, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7160 -> bs))
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
              (let uu____7179 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7179 e.FStar_Syntax_Syntax.pos)
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
          let uu____7201 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7201
          then e
          else
            (let uu____7203 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7203
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
        (let uu____7229 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7229
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7231 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7231))
         else ());
        (let fv =
           let uu____7234 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7234 None in
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
         let uu____7241 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___147_7250 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_7250.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_7250.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_7250.FStar_Syntax_Syntax.sigmeta)
           }), uu____7241))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7260 =
        match uu___105_7260 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7261 -> false in
      let reducibility uu___106_7265 =
        match uu___106_7265 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7266 -> false in
      let assumption uu___107_7270 =
        match uu___107_7270 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7271 -> false in
      let reification uu___108_7275 =
        match uu___108_7275 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7276 -> true
        | uu____7277 -> false in
      let inferred uu___109_7281 =
        match uu___109_7281 with
        | FStar_Syntax_Syntax.Discriminator uu____7282 -> true
        | FStar_Syntax_Syntax.Projector uu____7283 -> true
        | FStar_Syntax_Syntax.RecordType uu____7286 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7291 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7296 -> false in
      let has_eq uu___110_7300 =
        match uu___110_7300 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7301 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7335 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7338 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7341 =
        let uu____7342 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7344  ->
                  match uu___111_7344 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7345 -> false)) in
        FStar_All.pipe_right uu____7342 Prims.op_Negation in
      if uu____7341
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7355 =
            let uu____7356 =
              let uu____7359 =
                let uu____7360 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7360 msg in
              (uu____7359, r) in
            FStar_Errors.Error uu____7356 in
          raise uu____7355 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7368 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7376 =
            let uu____7377 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7377 in
          if uu____7376 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7381),uu____7382,uu____7383) ->
              ((let uu____7394 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7394
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7397 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7397
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7401 ->
              let uu____7406 =
                let uu____7407 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7407 in
              if uu____7406 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7411 ->
              let uu____7415 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7415 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7418 ->
              let uu____7422 =
                let uu____7423 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7423 in
              if uu____7422 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7427 ->
              let uu____7428 =
                let uu____7429 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7429 in
              if uu____7428 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7433 ->
              let uu____7434 =
                let uu____7435 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7435 in
              if uu____7434 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7439 ->
              let uu____7446 =
                let uu____7447 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7447 in
              if uu____7446 then err'1 () else ()
          | uu____7451 -> ()))
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
                        FStar_Syntax_Syntax.gen_bv "projectee" (Some p) ptyp in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs in
                      let tps = inductive_tps in
                      let arg_typ =
                        let inst_tc =
                          let uu____7507 =
                            let uu____7510 =
                              let uu____7511 =
                                let uu____7516 =
                                  let uu____7517 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7517 in
                                (uu____7516, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7511 in
                            FStar_Syntax_Syntax.mk uu____7510 in
                          uu____7507 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7543  ->
                                  match uu____7543 with
                                  | (x,imp) ->
                                      let uu____7550 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7550, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7554 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7554 in
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
                             let uu____7563 =
                               let uu____7564 =
                                 let uu____7565 =
                                   let uu____7566 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7567 =
                                     let uu____7568 =
                                       let uu____7569 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7569 in
                                     [uu____7568] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7566
                                     uu____7567 in
                                 uu____7565 None p in
                               FStar_Syntax_Util.b2t uu____7564 in
                             FStar_Syntax_Util.refine x uu____7563 in
                           let uu____7574 =
                             let uu___148_7575 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_7575.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_7575.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7574) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7585 =
                          FStar_List.map
                            (fun uu____7595  ->
                               match uu____7595 with
                               | (x,uu____7602) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7585 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7626  ->
                                match uu____7626 with
                                | (x,uu____7633) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7642 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7642)
                               ||
                               (let uu____7643 =
                                  let uu____7644 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7644.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7643) in
                           let quals =
                             let uu____7647 =
                               let uu____7649 =
                                 let uu____7651 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7651
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7654 =
                                 FStar_List.filter
                                   (fun uu___112_7656  ->
                                      match uu___112_7656 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7657 -> false) iquals in
                               FStar_List.append uu____7649 uu____7654 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7647 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7670 =
                                 let uu____7671 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7671 in
                               FStar_Syntax_Syntax.mk_Total uu____7670 in
                             let uu____7672 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7672 in
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
                           (let uu____7675 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7675
                            then
                              let uu____7676 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7676
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
                                             fun uu____7701  ->
                                               match uu____7701 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7715 =
                                                       let uu____7717 =
                                                         let uu____7718 =
                                                           let uu____7723 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7723,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7718 in
                                                       pos uu____7717 in
                                                     (uu____7715, b)
                                                   else
                                                     (let uu____7726 =
                                                        let uu____7728 =
                                                          let uu____7729 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7729 in
                                                        pos uu____7728 in
                                                      (uu____7726, b)))) in
                                   let pat_true =
                                     let uu____7739 =
                                       let uu____7741 =
                                         let uu____7742 =
                                           let uu____7749 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7749, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7742 in
                                       pos uu____7741 in
                                     (uu____7739, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7768 =
                                       let uu____7770 =
                                         let uu____7771 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7771 in
                                       pos uu____7770 in
                                     (uu____7768, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7779 =
                                     let uu____7782 =
                                       let uu____7783 =
                                         let uu____7798 =
                                           let uu____7800 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7801 =
                                             let uu____7803 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7803] in
                                           uu____7800 :: uu____7801 in
                                         (arg_exp, uu____7798) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7783 in
                                     FStar_Syntax_Syntax.mk uu____7782 in
                                   uu____7779 None p) in
                              let dd =
                                let uu____7814 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7814
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
                                let uu____7826 =
                                  let uu____7829 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7829 in
                                let uu____7830 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7826;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7830
                                } in
                              let impl =
                                let uu____7834 =
                                  let uu____7835 =
                                    let uu____7841 =
                                      let uu____7843 =
                                        let uu____7844 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7844
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7843] in
                                    ((false, [lb]), uu____7841, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7835 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7834;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7855 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7855
                               then
                                 let uu____7856 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7856
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
                                fun uu____7876  ->
                                  match uu____7876 with
                                  | (a,uu____7880) ->
                                      let uu____7881 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7881 with
                                       | (field_name,uu____7885) ->
                                           let field_proj_tm =
                                             let uu____7887 =
                                               let uu____7888 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7888 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7887 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7902 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7911  ->
                                    match uu____7911 with
                                    | (x,uu____7916) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____7918 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____7918 with
                                         | (field_name,uu____7923) ->
                                             let t =
                                               let uu____7925 =
                                                 let uu____7926 =
                                                   let uu____7929 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7929 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7926 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7925 in
                                             let only_decl =
                                               ((let uu____7931 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7931)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7932 =
                                                    let uu____7933 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____7933.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7932) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7943 =
                                                   FStar_List.filter
                                                     (fun uu___113_7945  ->
                                                        match uu___113_7945
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7946 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7943
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_7954  ->
                                                         match uu___114_7954
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____7955 ->
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
                                             ((let uu____7958 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____7958
                                               then
                                                 let uu____7959 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7959
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
                                                           fun uu____7983  ->
                                                             match uu____7983
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7997
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____7997,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8006
                                                                    =
                                                                    let uu____8008
                                                                    =
                                                                    let uu____8009
                                                                    =
                                                                    let uu____8014
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8014,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8009 in
                                                                    pos
                                                                    uu____8008 in
                                                                    (uu____8006,
                                                                    b))
                                                                   else
                                                                    (let uu____8017
                                                                    =
                                                                    let uu____8019
                                                                    =
                                                                    let uu____8020
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8020 in
                                                                    pos
                                                                    uu____8019 in
                                                                    (uu____8017,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8030 =
                                                     let uu____8032 =
                                                       let uu____8033 =
                                                         let uu____8040 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8040,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8033 in
                                                     pos uu____8032 in
                                                   let uu____8045 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8030, None,
                                                     uu____8045) in
                                                 let body =
                                                   let uu____8055 =
                                                     let uu____8058 =
                                                       let uu____8059 =
                                                         let uu____8074 =
                                                           let uu____8076 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8076] in
                                                         (arg_exp,
                                                           uu____8074) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8059 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8058 in
                                                   uu____8055 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8093 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8093
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
                                                   let uu____8099 =
                                                     let uu____8102 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8102 in
                                                   let uu____8103 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8099;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8103
                                                   } in
                                                 let impl =
                                                   let uu____8107 =
                                                     let uu____8108 =
                                                       let uu____8114 =
                                                         let uu____8116 =
                                                           let uu____8117 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8117
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8116] in
                                                       ((false, [lb]),
                                                         uu____8114, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8108 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8107;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8128 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8128
                                                  then
                                                    let uu____8129 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8129
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7902 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8159) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8162 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8162 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8175 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8175 with
                    | (formals,uu____8185) ->
                        let uu____8196 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8209 =
                                   let uu____8210 =
                                     let uu____8211 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8211 in
                                   FStar_Ident.lid_equals typ_lid uu____8210 in
                                 if uu____8209
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8221,uvs',tps,typ0,uu____8225,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8238 -> failwith "Impossible"
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
                        (match uu____8196 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8280 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8280 with
                              | (indices,uu____8290) ->
                                  let refine_domain =
                                    let uu____8302 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8304  ->
                                              match uu___115_8304 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8305 -> true
                                              | uu____8310 -> false)) in
                                    if uu____8302
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8317 =
                                      match uu___116_8317 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8319,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8326 -> None in
                                    let uu____8327 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8327 with
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
                                    let uu____8335 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8335 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8366  ->
                                               fun uu____8367  ->
                                                 match (uu____8366,
                                                         uu____8367)
                                                 with
                                                 | ((x,uu____8377),(x',uu____8379))
                                                     ->
                                                     let uu____8384 =
                                                       let uu____8389 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8389) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8384) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8390 -> []