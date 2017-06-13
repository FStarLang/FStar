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
                          let uu___120_814 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___120_814.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___120_814.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____821 = FStar_Syntax_Util.type_u () in
              (match uu____821 with
               | (t,uu____834) ->
                   let x1 =
                     let uu___121_836 = x in
                     let uu____837 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_836.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_836.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____837
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
              let uu____859 = FStar_Syntax_Util.type_u () in
              (match uu____859 with
               | (t,uu____872) ->
                   let x1 =
                     let uu___122_874 = x in
                     let uu____875 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_874.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_874.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____875
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____907 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____963  ->
                        fun uu____964  ->
                          match (uu____963, uu____964) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1063 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1063 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____907 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1171 =
                       let uu____1174 =
                         let uu____1175 =
                           let uu____1180 =
                             let uu____1183 =
                               let uu____1184 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1185 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1184
                                 uu____1185 in
                             uu____1183 None p1.FStar_Syntax_Syntax.p in
                           (uu____1180,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1175 in
                       FStar_Syntax_Syntax.mk uu____1174 in
                     uu____1171 None p1.FStar_Syntax_Syntax.p in
                   let uu____1202 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1208 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1214 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1202, uu____1208, uu____1214, env2, e,
                     (let uu___123_1227 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___123_1227.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___123_1227.FStar_Syntax_Syntax.p)
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
                  (fun uu____1289  ->
                     match uu____1289 with
                     | (p2,imp) ->
                         let uu____1304 = elaborate_pat env1 p2 in
                         (uu____1304, imp)) pats in
              let uu____1309 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1309 with
               | (uu____1318,t) ->
                   let uu____1320 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1320 with
                    | (f,uu____1331) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1406::uu____1407) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1442::uu____1443,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1483  ->
                                      match uu____1483 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1501 =
                                                   let uu____1503 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1503 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1501
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1509 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1509, true)
                                           | uu____1514 ->
                                               let uu____1516 =
                                                 let uu____1517 =
                                                   let uu____1520 =
                                                     let uu____1521 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1521 in
                                                   (uu____1520,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1517 in
                                               raise uu____1516)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1572,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1573))
                                   when p_imp ->
                                   let uu____1575 = aux formals' pats' in
                                   (p2, true) :: uu____1575
                               | (uu____1587,Some
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
                                   let uu____1598 = aux formals' pats2 in
                                   (p3, true) :: uu____1598
                               | (uu____1610,imp) ->
                                   let uu____1614 =
                                     let uu____1619 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1619) in
                                   let uu____1622 = aux formals' pats' in
                                   uu____1614 :: uu____1622) in
                        let uu___124_1632 = p1 in
                        let uu____1635 =
                          let uu____1636 =
                            let uu____1644 = aux f pats1 in (fv, uu____1644) in
                          FStar_Syntax_Syntax.Pat_cons uu____1636 in
                        {
                          FStar_Syntax_Syntax.v = uu____1635;
                          FStar_Syntax_Syntax.ty =
                            (uu___124_1632.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___124_1632.FStar_Syntax_Syntax.p)
                        }))
          | uu____1655 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1681 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1681 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1711 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1711 with
               | Some x ->
                   let uu____1724 =
                     let uu____1725 =
                       let uu____1728 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1728, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1725 in
                   raise uu____1724
               | uu____1737 -> (b, a, w, arg, p3)) in
        let uu____1742 = one_pat true env p in
        match uu____1742 with
        | (b,uu____1756,uu____1757,tm,p1) -> (b, tm, p1)
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
          | (uu____1798,FStar_Syntax_Syntax.Tm_uinst (e2,uu____1800)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____1805,FStar_Syntax_Syntax.Tm_constant uu____1806) ->
              let uu____1807 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____1807
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____1811 =
                    let uu____1812 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1813 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1812 uu____1813 in
                  failwith uu____1811)
               else ();
               (let uu____1816 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____1816
                then
                  let uu____1817 = FStar_Syntax_Print.bv_to_string x in
                  let uu____1818 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____1817
                    uu____1818
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___125_1822 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_1822.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_1822.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____1826 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____1826
                then
                  let uu____1827 =
                    let uu____1828 = FStar_Syntax_Print.bv_to_string x in
                    let uu____1829 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____1828 uu____1829 in
                  failwith uu____1827
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_1833 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_1833.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_1833.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____1835),uu____1836) ->
              let s = force_sort e1 in
              let x1 =
                let uu___127_1845 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___127_1845.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___127_1845.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____1858 =
                  let uu____1859 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____1859 in
                if uu____1858
                then
                  let uu____1860 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1860
                else ());
               (let uu____1870 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____1870))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____1883;
                FStar_Syntax_Syntax.pos = uu____1884;
                FStar_Syntax_Syntax.vars = uu____1885;_},args))
              ->
              ((let uu____1912 =
                  let uu____1913 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____1913 Prims.op_Negation in
                if uu____1912
                then
                  let uu____1914 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____1914
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2002 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2002
                  | (arg::args2,(argpat,uu____2015)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2065) ->
                           let x =
                             let uu____2081 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2081 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2095) ->
                           let pat =
                             let uu____2110 = aux argpat e2 in
                             let uu____2111 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2110, uu____2111) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2114 ->
                      let uu____2128 =
                        let uu____2129 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2130 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2129 uu____2130 in
                      failwith uu____2128 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2140;
                     FStar_Syntax_Syntax.pos = uu____2141;
                     FStar_Syntax_Syntax.vars = uu____2142;_},uu____2143);
                FStar_Syntax_Syntax.tk = uu____2144;
                FStar_Syntax_Syntax.pos = uu____2145;
                FStar_Syntax_Syntax.vars = uu____2146;_},args))
              ->
              ((let uu____2177 =
                  let uu____2178 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2178 Prims.op_Negation in
                if uu____2177
                then
                  let uu____2179 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2179
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2267 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2267
                  | (arg::args2,(argpat,uu____2280)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2330) ->
                           let x =
                             let uu____2346 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2346 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2360) ->
                           let pat =
                             let uu____2375 = aux argpat e2 in
                             let uu____2376 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2375, uu____2376) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2379 ->
                      let uu____2393 =
                        let uu____2394 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2395 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2394 uu____2395 in
                      failwith uu____2393 in
                match_args [] args argpats))
          | uu____2402 ->
              let uu____2405 =
                let uu____2406 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2407 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2408 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2406 uu____2407 uu____2408 in
              failwith uu____2405 in
        aux p exp
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2442 =
      match uu____2442 with
      | (p,i) ->
          let uu____2452 = decorated_pattern_as_term p in
          (match uu____2452 with
           | (vars,te) ->
               let uu____2465 =
                 let uu____2468 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2468) in
               (vars, uu____2465)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2476 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2476)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2479 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2479)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2482 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2482)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2496 =
          let uu____2504 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2504 FStar_List.unzip in
        (match uu____2496 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2562 =
               let uu____2563 =
                 let uu____2564 =
                   let uu____2574 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2574, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2564 in
               mk1 uu____2563 in
             (vars1, uu____2562))
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
      | (wp,uu____2603)::[] -> wp
      | uu____2616 ->
          let uu____2622 =
            let uu____2623 =
              let uu____2624 =
                FStar_List.map
                  (fun uu____2628  ->
                     match uu____2628 with
                     | (x,uu____2632) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2624 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2623 in
          failwith uu____2622 in
    let uu____2636 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2636, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2650 = destruct_comp c in
        match uu____2650 with
        | (u,uu____2655,wp) ->
            let uu____2657 =
              let uu____2663 =
                let uu____2664 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2664 in
              [uu____2663] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2657;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2674 =
          let uu____2678 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2679 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2678 uu____2679 in
        match uu____2674 with | (m,uu____2681,uu____2682) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2692 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2692
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
        let uu____2717 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2717 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2739 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2739 with
             | (a,kwp) ->
                 let uu____2756 = destruct_comp m1 in
                 let uu____2760 = destruct_comp m2 in
                 ((md, a, kwp), uu____2756, uu____2760))
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
            let uu____2808 =
              let uu____2809 =
                let uu____2815 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2815] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2809;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2808
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
      let uu___128_2851 = lc in
      let uu____2852 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___128_2851.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2852;
        FStar_Syntax_Syntax.cflags =
          (uu___128_2851.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2855  ->
             let uu____2856 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2856)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2860 =
      let uu____2861 = FStar_Syntax_Subst.compress t in
      uu____2861.FStar_Syntax_Syntax.n in
    match uu____2860 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2864 -> true
    | uu____2872 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2884 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2884
        then c
        else
          (let uu____2886 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2886
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2916 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2916] in
                       let us =
                         let uu____2919 =
                           let uu____2921 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2921] in
                         u_res :: uu____2919 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2932 =
                         let uu____2933 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2934 =
                           let uu____2935 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2936 =
                             let uu____2938 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2939 =
                               let uu____2941 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____2941] in
                             uu____2938 :: uu____2939 in
                           uu____2935 :: uu____2936 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2933 uu____2934 in
                       uu____2932 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____2947 = destruct_comp c1 in
              match uu____2947 with
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
        let close1 uu____2970 =
          let uu____2971 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____2971 in
        let uu___129_2972 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___129_2972.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___129_2972.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___129_2972.FStar_Syntax_Syntax.cflags);
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
          let uu____2983 =
            let uu____2984 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____2984 in
          if uu____2983
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____2989 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____2989
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2991 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____2991 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____2997 =
                        let uu____2998 =
                          let uu____2999 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3000 =
                            let uu____3001 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3002 =
                              let uu____3004 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3004] in
                            uu____3001 :: uu____3002 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2999 uu____3000 in
                        uu____2998 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2997) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3010 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3010
         then
           let uu____3011 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3012 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3013 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3011
             uu____3012 uu____3013
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
          fun uu____3030  ->
            match uu____3030 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3040 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3040
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3043 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3045 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3046 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3043 uu____3045 bstr uu____3046
                  else ());
                 (let bind_it uu____3051 =
                    let uu____3052 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3052
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3062 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3062
                        then
                          let uu____3063 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3065 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3066 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3067 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3068 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3063 uu____3065 uu____3066 uu____3067
                            uu____3068
                        else ());
                       (let try_simplify uu____3079 =
                          let aux uu____3089 =
                            let uu____3090 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3090
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3109 ->
                                  let uu____3110 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3110
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3129 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3129
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3165 =
                                  let uu____3168 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3168, reason) in
                                FStar_Util.Inl uu____3165
                            | uu____3171 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3186 =
                              let uu____3187 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3187.FStar_Syntax_Syntax.n in
                            match uu____3186 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3191) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3197 -> c in
                          let uu____3198 =
                            let uu____3199 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3199 in
                          if uu____3198
                          then
                            let uu____3207 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3207
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3221 =
                                  let uu____3222 =
                                    let uu____3225 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3225) in
                                  FStar_Errors.Error uu____3222 in
                                raise uu____3221))
                          else
                            (let uu____3233 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3233
                             then subst_c2 "both total"
                             else
                               (let uu____3241 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3241
                                then
                                  let uu____3248 =
                                    let uu____3251 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3251, "both gtot") in
                                  FStar_Util.Inl uu____3248
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3267 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3268 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3268) in
                                       if uu____3267
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___130_3277 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___130_3277.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___130_3277.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3278 =
                                           let uu____3281 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3281, "c1 Tot") in
                                         FStar_Util.Inl uu____3278
                                       else aux ()
                                   | uu____3285 -> aux ()))) in
                        let uu____3290 = try_simplify () in
                        match uu____3290 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3308 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3308
                              then
                                let uu____3309 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3310 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3311 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3309 uu____3310 uu____3311
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3318 = lift_and_destruct env c1 c2 in
                            (match uu____3318 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3352 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3352]
                                   | Some x ->
                                       let uu____3354 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3354] in
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
                                   let uu____3377 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3378 =
                                     let uu____3380 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3381 =
                                       let uu____3383 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3384 =
                                         let uu____3386 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3387 =
                                           let uu____3389 =
                                             let uu____3390 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3390 in
                                           [uu____3389] in
                                         uu____3386 :: uu____3387 in
                                       uu____3383 :: uu____3384 in
                                     uu____3380 :: uu____3381 in
                                   uu____3377 :: uu____3378 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3395 =
                                     let uu____3396 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3396
                                       wp_args in
                                   uu____3395 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3440 =
                let uu____3441 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3441 in
              if uu____3440
              then f
              else (let uu____3443 = reason1 () in label uu____3443 r f)
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
            let uu___131_3454 = g in
            let uu____3455 =
              let uu____3456 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3456 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3455;
              FStar_TypeChecker_Env.deferred =
                (uu___131_3454.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_3454.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_3454.FStar_TypeChecker_Env.implicits)
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
      | uu____3466 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3483 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3487 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3487
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3494 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3494
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3499 = destruct_comp c1 in
                    match uu____3499 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3512 =
                            let uu____3513 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3514 =
                              let uu____3515 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3516 =
                                let uu____3518 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3519 =
                                  let uu____3521 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3521] in
                                uu____3518 :: uu____3519 in
                              uu____3515 :: uu____3516 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3513
                              uu____3514 in
                          uu____3512 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___132_3526 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___132_3526.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___132_3526.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___132_3526.FStar_Syntax_Syntax.cflags);
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
            let uu____3553 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3553
            then (lc, g0)
            else
              ((let uu____3558 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3558
                then
                  let uu____3559 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3560 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3559 uu____3560
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3566  ->
                          match uu___98_3566 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3568 -> [])) in
                let strengthen uu____3574 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3582 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3582 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3589 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3590 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3590) in
                           if uu____3589
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3597 =
                                 let uu____3598 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3598 in
                               FStar_Syntax_Util.comp_set_flags uu____3597
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3603 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3603
                           then
                             let uu____3604 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3605 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3604 uu____3605
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3608 = destruct_comp c2 in
                           match uu____3608 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3621 =
                                   let uu____3622 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3623 =
                                     let uu____3624 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3625 =
                                       let uu____3627 =
                                         let uu____3628 =
                                           let uu____3629 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3629 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3628 in
                                       let uu____3630 =
                                         let uu____3632 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3632] in
                                       uu____3627 :: uu____3630 in
                                     uu____3624 :: uu____3625 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3622
                                     uu____3623 in
                                 uu____3621 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3638 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3638
                                 then
                                   let uu____3639 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3639
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3642 =
                  let uu___133_3643 = lc in
                  let uu____3644 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3645 =
                    let uu____3647 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3648 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3648) in
                    if uu____3647 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3644;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___133_3643.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3645;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3642,
                  (let uu___134_3651 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___134_3651.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___134_3651.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___134_3651.FStar_TypeChecker_Env.implicits)
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
        let uu____3666 =
          let uu____3669 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3670 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3669, uu____3670) in
        match uu____3666 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3679 =
                let uu____3680 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3681 =
                  let uu____3682 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3683 =
                    let uu____3685 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3685] in
                  uu____3682 :: uu____3683 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3680 uu____3681 in
              uu____3679 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3693 =
                let uu____3694 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3695 =
                  let uu____3696 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3697 =
                    let uu____3699 =
                      let uu____3700 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3700 in
                    let uu____3701 =
                      let uu____3703 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3703] in
                    uu____3699 :: uu____3701 in
                  uu____3696 :: uu____3697 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3694 uu____3695 in
              uu____3693 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3711 =
                let uu____3712 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3713 =
                  let uu____3714 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3715 =
                    let uu____3717 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3718 =
                      let uu____3720 =
                        let uu____3721 =
                          let uu____3722 =
                            let uu____3723 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3723] in
                          FStar_Syntax_Util.abs uu____3722 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3721 in
                      [uu____3720] in
                    uu____3717 :: uu____3718 in
                  uu____3714 :: uu____3715 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3712 uu____3713 in
              uu____3711 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3739 = FStar_TypeChecker_Env.get_range env in
              bind uu____3739 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3757 =
            let uu____3758 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3758
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3761 =
                 let uu____3774 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3775 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3774 uu____3775 in
               match uu____3761 with
               | ((md,uu____3777,uu____3778),(u_res_t,res_t,wp_then),
                  (uu____3782,uu____3783,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3812 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3813 =
                       let uu____3814 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3815 =
                         let uu____3816 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3817 =
                           let uu____3819 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3820 =
                             let uu____3822 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3823 =
                               let uu____3825 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3825] in
                             uu____3822 :: uu____3823 in
                           uu____3819 :: uu____3820 in
                         uu____3816 :: uu____3817 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3814 uu____3815 in
                     uu____3813 None uu____3812 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3833 =
                     let uu____3834 = FStar_Options.split_cases () in
                     uu____3834 > (Prims.parse_int "0") in
                   if uu____3833
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3840 =
                          let uu____3841 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3842 =
                            let uu____3843 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3844 =
                              let uu____3846 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3846] in
                            uu____3843 :: uu____3844 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3841 uu____3842 in
                        uu____3840 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3851 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3851;
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
      let uu____3858 =
        let uu____3859 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3859 in
      FStar_Syntax_Syntax.fvar uu____3858 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3879  ->
                 match uu____3879 with
                 | (uu____3882,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3887 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3889 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3889
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3909 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3910 =
                 let uu____3911 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3912 =
                   let uu____3913 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3914 =
                     let uu____3916 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3917 =
                       let uu____3919 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3920 =
                         let uu____3922 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3922] in
                       uu____3919 :: uu____3920 in
                     uu____3916 :: uu____3917 in
                   uu____3913 :: uu____3914 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3911 uu____3912 in
               uu____3910 None uu____3909 in
             let default_case =
               let post_k =
                 let uu____3931 =
                   let uu____3935 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3935] in
                 let uu____3936 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3931 uu____3936 in
               let kwp =
                 let uu____3942 =
                   let uu____3946 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____3946] in
                 let uu____3947 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3942 uu____3947 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____3952 =
                   let uu____3953 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____3953] in
                 let uu____3954 =
                   let uu____3955 =
                     let uu____3958 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____3958 in
                   let uu____3959 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____3955 uu____3959 in
                 FStar_Syntax_Util.abs uu____3952 uu____3954
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
                 (fun uu____3973  ->
                    fun celse  ->
                      match uu____3973 with
                      | (g,cthen) ->
                          let uu____3979 =
                            let uu____3992 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____3992 celse in
                          (match uu____3979 with
                           | ((md,uu____3994,uu____3995),(uu____3996,uu____3997,wp_then),
                              (uu____3999,uu____4000,wp_else)) ->
                               let uu____4011 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4011 []))
                 lcases default_case in
             let uu____4012 =
               let uu____4013 = FStar_Options.split_cases () in
               uu____4013 > (Prims.parse_int "0") in
             if uu____4012
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4017 = destruct_comp comp1 in
                match uu____4017 with
                | (uu____4021,uu____4022,wp) ->
                    let wp1 =
                      let uu____4027 =
                        let uu____4028 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4029 =
                          let uu____4030 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4031 =
                            let uu____4033 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4033] in
                          uu____4030 :: uu____4031 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4028 uu____4029 in
                      uu____4027 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4049 =
            ((let uu____4050 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4050) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4051 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4051) in
          if uu____4049
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4059 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4063 =
            (let uu____4064 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4064) || env.FStar_TypeChecker_Env.lax in
          if uu____4063
          then c
          else
            (let uu____4068 = FStar_Syntax_Util.is_partial_return c in
             if uu____4068
             then c
             else
               (let uu____4072 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4072
                then
                  let uu____4075 =
                    let uu____4076 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4076 in
                  (if uu____4075
                   then
                     let uu____4079 =
                       let uu____4080 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4081 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4080 uu____4081 in
                     failwith uu____4079
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4086 =
                        let uu____4087 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4087 in
                      if uu____4086
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___135_4092 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___135_4092.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___135_4092.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___135_4092.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4103 =
                       let uu____4106 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4106
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4103 in
                   let eq1 =
                     let uu____4110 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4110 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4112 =
                     let uu____4113 =
                       let uu____4118 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4118.FStar_Syntax_Syntax.comp in
                     uu____4113 () in
                   FStar_Syntax_Util.comp_set_flags uu____4112 flags))) in
        let uu___136_4120 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___136_4120.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___136_4120.FStar_Syntax_Syntax.res_typ);
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
          let uu____4139 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4139 with
          | None  ->
              let uu____4144 =
                let uu____4145 =
                  let uu____4148 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4149 = FStar_TypeChecker_Env.get_range env in
                  (uu____4148, uu____4149) in
                FStar_Errors.Error uu____4145 in
              raise uu____4144
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
            let uu____4175 =
              let uu____4176 = FStar_Syntax_Subst.compress t2 in
              uu____4176.FStar_Syntax_Syntax.n in
            match uu____4175 with
            | FStar_Syntax_Syntax.Tm_type uu____4179 -> true
            | uu____4180 -> false in
          let uu____4181 =
            let uu____4182 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4182.FStar_Syntax_Syntax.n in
          match uu____4181 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4188 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4195 =
                  let uu____4196 =
                    let uu____4197 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4197 in
                  (None, uu____4196) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4195 in
              let e1 =
                let uu____4206 =
                  let uu____4207 =
                    let uu____4208 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4208] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4207 in
                uu____4206
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4215 -> (e, lc)
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
              (let uu____4235 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4235 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4248 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4260 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4260, false)
            else
              (let uu____4264 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4264, true)) in
          match gopt with
          | (None ,uu____4270) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___137_4273 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___137_4273.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___137_4273.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___137_4273.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4277 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4277 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___138_4282 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___138_4282.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___138_4282.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___138_4282.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4285 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4285.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4285.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4285.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4291 =
                     let uu____4292 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4292
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4297 =
                          let uu____4298 = FStar_Syntax_Subst.compress f1 in
                          uu____4298.FStar_Syntax_Syntax.n in
                        match uu____4297 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4303,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4305;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4306;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4307;_},uu____4308)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4332 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___140_4332.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___140_4332.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___140_4332.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4333 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4338 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4338
                              then
                                let uu____4339 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4340 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4341 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4342 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4339 uu____4340 uu____4341 uu____4342
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4345 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4345 with
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
                                  let uu____4356 = destruct_comp ct in
                                  (match uu____4356 with
                                   | (u_t,uu____4363,uu____4364) ->
                                       let wp =
                                         let uu____4368 =
                                           let uu____4369 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4370 =
                                             let uu____4371 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4372 =
                                               let uu____4374 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4374] in
                                             uu____4371 :: uu____4372 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4369 uu____4370 in
                                         uu____4368
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4380 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4380 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4390 =
                                             let uu____4391 =
                                               let uu____4392 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4392] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4391 in
                                           uu____4390
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4398 =
                                         let uu____4401 =
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4412 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4413 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4401
                                           uu____4412 e cret uu____4413 in
                                       (match uu____4398 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___141_4419 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___141_4419.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___141_4419.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4421 =
                                                let uu____4422 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4422 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4421
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4432 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4432
                                              then
                                                let uu____4433 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4433
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4439  ->
                             match uu___99_4439 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4441 -> [])) in
                   let lc1 =
                     let uu___142_4443 = lc in
                     let uu____4444 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4444;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___143_4446 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4446.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4446.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4446.FStar_TypeChecker_Env.implicits)
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
        let uu____4466 =
          let uu____4467 =
            let uu____4468 =
              let uu____4469 =
                let uu____4470 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4470 in
              [uu____4469] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4468 in
          uu____4467 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4466 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4479 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4479
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4490 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4499 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4516)::(ens,uu____4518)::uu____4519 ->
                    let uu____4541 =
                      let uu____4543 = norm req in Some uu____4543 in
                    let uu____4544 =
                      let uu____4545 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4545 in
                    (uu____4541, uu____4544)
                | uu____4547 ->
                    let uu____4553 =
                      let uu____4554 =
                        let uu____4557 =
                          let uu____4558 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4558 in
                        (uu____4557, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4554 in
                    raise uu____4553)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4568)::uu____4569 ->
                    let uu____4583 =
                      let uu____4586 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4586 in
                    (match uu____4583 with
                     | (us_r,uu____4603) ->
                         let uu____4604 =
                           let uu____4607 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4607 in
                         (match uu____4604 with
                          | (us_e,uu____4624) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4627 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4627
                                  us_r in
                              let as_ens =
                                let uu____4629 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4629
                                  us_e in
                              let req =
                                let uu____4633 =
                                  let uu____4634 =
                                    let uu____4635 =
                                      let uu____4642 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4642] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4635 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4634 in
                                uu____4633
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4658 =
                                  let uu____4659 =
                                    let uu____4660 =
                                      let uu____4667 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4667] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4660 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4659 in
                                uu____4658 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4680 =
                                let uu____4682 = norm req in Some uu____4682 in
                              let uu____4683 =
                                let uu____4684 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4684 in
                              (uu____4680, uu____4683)))
                | uu____4686 -> failwith "Impossible"))
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
      (let uu____4706 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4706
       then
         let uu____4707 = FStar_Syntax_Print.term_to_string tm in
         let uu____4708 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4707 uu____4708
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
        (let uu____4729 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4729
         then
           let uu____4730 = FStar_Syntax_Print.term_to_string tm in
           let uu____4731 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4730
             uu____4731
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4736 =
      let uu____4737 =
        let uu____4738 = FStar_Syntax_Subst.compress t in
        uu____4738.FStar_Syntax_Syntax.n in
      match uu____4737 with
      | FStar_Syntax_Syntax.Tm_app uu____4741 -> false
      | uu____4751 -> true in
    if uu____4736
    then t
    else
      (let uu____4753 = FStar_Syntax_Util.head_and_args t in
       match uu____4753 with
       | (head1,args) ->
           let uu____4779 =
             let uu____4780 =
               let uu____4781 = FStar_Syntax_Subst.compress head1 in
               uu____4781.FStar_Syntax_Syntax.n in
             match uu____4780 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4784 -> false in
           if uu____4779
           then
             (match args with
              | x::[] -> fst x
              | uu____4800 ->
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
             let uu____4828 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4828 with
             | (formals,uu____4837) ->
                 let n_implicits =
                   let uu____4849 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4886  ->
                             match uu____4886 with
                             | (uu____4890,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4849 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____4962 = FStar_TypeChecker_Env.expected_typ env in
             match uu____4962 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____4976 =
                     let uu____4977 =
                       let uu____4980 =
                         let uu____4981 = FStar_Util.string_of_int n_expected in
                         let uu____4985 = FStar_Syntax_Print.term_to_string e in
                         let uu____4986 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4981 uu____4985 uu____4986 in
                       let uu____4990 = FStar_TypeChecker_Env.get_range env in
                       (uu____4980, uu____4990) in
                     FStar_Errors.Error uu____4977 in
                   raise uu____4976
                 else Some (n_available - n_expected) in
           let decr_inst uu___100_5003 =
             match uu___100_5003 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5022 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5022 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_30,uu____5083) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5105,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5124 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5124 with
                           | (v1,uu____5145,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5155 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5155 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5204 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5204)))
                      | (uu____5218,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5242 =
                      let uu____5256 = inst_n_binders t in
                      aux [] uu____5256 bs1 in
                    (match uu____5242 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5294) -> (e, torig, guard)
                          | (uu____5310,[]) when
                              let uu____5326 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5326 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5327 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5346 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5361 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____5367 =
      let uu____5369 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____5369
        (FStar_List.map
           (fun u  ->
              let uu____5374 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____5374 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____5367 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5386 = FStar_Util.set_is_empty x in
      if uu____5386
      then []
      else
        (let s =
           let uu____5391 =
             let uu____5393 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5393 in
           FStar_All.pipe_right uu____5391 FStar_Util.set_elements in
         (let uu____5398 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5398
          then
            let uu____5399 =
              let uu____5400 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5400 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5399
          else ());
         (let r =
            let uu____5405 = FStar_TypeChecker_Env.get_range env in
            Some uu____5405 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5413 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5413
                     then
                       let uu____5414 =
                         let uu____5415 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5415 in
                       let uu____5416 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5417 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5414 uu____5416 uu____5417
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
        let uu____5434 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5434 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5461 =
  match uu___101_5461 with
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
      (let uu____5534 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5534
       then
         let uu____5535 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5535
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5540 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5540
        then
          let uu____5541 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5541
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in
        let uu____5547 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5547))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5577 =
        let uu____5578 =
          FStar_Util.for_all
            (fun uu____5583  ->
               match uu____5583 with
               | (uu____5588,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5578 in
      if uu____5577
      then None
      else
        (let norm c =
           (let uu____5611 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5611
            then
              let uu____5612 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5612
            else ());
           (let c1 =
              let uu____5615 = FStar_TypeChecker_Env.should_verify env in
              if uu____5615
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5618 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5618
             then
               let uu____5619 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5619
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5659 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5659 FStar_Util.set_elements in
         let uu____5713 =
           let uu____5733 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5794  ->
                     match uu____5794 with
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
           FStar_All.pipe_right uu____5733 FStar_List.unzip in
         match uu____5713 with
         | (univs1,uvars1) ->
             let univs2 =
               let uu____5969 = FStar_Syntax_Free.new_universe_uvar_set () in
               FStar_List.fold_left FStar_Util.set_union uu____5969 univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____5976 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____5976
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
                      (fun uu____6016  ->
                         match uu____6016 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6053  ->
                                       match uu____6053 with
                                       | (u,k) ->
                                           let uu____6061 =
                                             FStar_Syntax_Unionfind.find u in
                                           (match uu____6061 with
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6067;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6068;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6069;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6075,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6077;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6078;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6079;_},uu____6080);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6081;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6082;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6083;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | Some uu____6111 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6115 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6118 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6118 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6142 =
                                                         let uu____6144 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              Some _0_31)
                                                           uu____6144 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6142 kres in
                                                     let t =
                                                       let uu____6147 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6148 =
                                                         let uu____6155 =
                                                           let uu____6161 =
                                                             let uu____6162 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6162 in
                                                           FStar_Util.Inl
                                                             uu____6161 in
                                                         Some uu____6155 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6147
                                                         uu____6148 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6175 =
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
                               | uu____6195 ->
                                   let uu____6203 = (e, c) in
                                   (match uu____6203 with
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
                                          let uu____6215 =
                                            let uu____6216 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6216.FStar_Syntax_Syntax.n in
                                          match uu____6215 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6233 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6233 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6243 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6253 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6253)) in
                             (match uu____6175 with
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
      (let uu____6291 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6291
       then
         let uu____6292 =
           let uu____6293 =
             FStar_List.map
               (fun uu____6298  ->
                  match uu____6298 with
                  | (lb,uu____6303,uu____6304) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6293 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6292
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6314  ->
              match uu____6314 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6329 =
           let uu____6336 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6352  ->
                     match uu____6352 with | (uu____6358,e,c) -> (e, c))) in
           gen env uu____6336 in
         match uu____6329 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6390  ->
                     match uu____6390 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6434  ->
                  fun uu____6435  ->
                    match (uu____6434, uu____6435) with
                    | ((l,uu____6468,uu____6469),(us,e,c)) ->
                        ((let uu____6495 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6495
                          then
                            let uu____6496 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6497 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6498 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6499 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6496 uu____6497 uu____6498 uu____6499
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6518  ->
              match uu____6518 with
              | (l,generalized_univs,t,c) ->
                  let uu____6536 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6536, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6569 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6569 with
               | None  -> None
               | Some f ->
                   let uu____6573 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____6573) in
          let is_var e1 =
            let uu____6579 =
              let uu____6580 = FStar_Syntax_Subst.compress e1 in
              uu____6580.FStar_Syntax_Syntax.n in
            match uu____6579 with
            | FStar_Syntax_Syntax.Tm_name uu____6583 -> true
            | uu____6584 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___144_6602 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_6602.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_6602.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6603 ->
                let uu___145_6604 = e2 in
                let uu____6605 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6604.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6605;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6604.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6604.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___146_6614 = env1 in
            let uu____6615 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6614.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6614.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6614.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6614.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6614.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6614.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6614.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6614.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6614.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6614.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6614.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6614.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6614.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6614.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6614.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6615;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6614.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6614.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6614.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6614.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6614.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6614.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6614.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6614.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6616 = check env2 t1 t2 in
          match uu____6616 with
          | None  ->
              let uu____6620 =
                let uu____6621 =
                  let uu____6624 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6625 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6624, uu____6625) in
                FStar_Errors.Error uu____6621 in
              raise uu____6620
          | Some g ->
              ((let uu____6630 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6630
                then
                  let uu____6631 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6631
                else ());
               (let uu____6633 = decorate e t2 in (uu____6633, g)))
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
        let uu____6657 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6657
        then
          let uu____6660 = discharge g1 in
          let uu____6661 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6660, uu____6661)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6673 =
               let uu____6674 =
                 let uu____6675 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6675 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6674
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6673
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6677 = destruct_comp c1 in
           match uu____6677 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6689 = FStar_TypeChecker_Env.get_range env in
                 let uu____6690 =
                   let uu____6691 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6692 =
                     let uu____6693 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6694 =
                       let uu____6696 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6696] in
                     uu____6693 :: uu____6694 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6691 uu____6692 in
                 uu____6690
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6689 in
               ((let uu____6702 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6702
                 then
                   let uu____6703 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6703
                 else ());
                (let g2 =
                   let uu____6706 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6706 in
                 let uu____6707 = discharge g2 in
                 let uu____6708 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6707, uu____6708))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6732 =
        match uu___102_6732 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6738)::[] -> f fst1
        | uu____6751 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6756 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6756
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____6765 =
          let uu____6768 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6768 in
        FStar_All.pipe_right uu____6765
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____6779 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6779
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_6793 =
        match uu___103_6793 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6799)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6814)::[] ->
            let uu____6835 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6835
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____6840 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6847 =
          let uu____6852 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6852) in
        let uu____6857 =
          let uu____6863 =
            let uu____6868 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6868) in
          let uu____6873 =
            let uu____6879 =
              let uu____6884 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6884) in
            let uu____6889 =
              let uu____6895 =
                let uu____6900 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6900) in
              let uu____6905 =
                let uu____6911 =
                  let uu____6916 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6916) in
                [uu____6911; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6895 :: uu____6905 in
            uu____6879 :: uu____6889 in
          uu____6863 :: uu____6873 in
        uu____6847 :: uu____6857 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____6957 =
            FStar_Util.find_map table
              (fun uu____6963  ->
                 match uu____6963 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6976 = mk1 seen_args in Some uu____6976
                     else None) in
          (match uu____6957 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6979 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6983 =
      let uu____6984 = FStar_Syntax_Util.un_uinst l in
      uu____6984.FStar_Syntax_Syntax.n in
    match uu____6983 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6988 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7006)::uu____7007 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7013 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7017,Some (FStar_Syntax_Syntax.Implicit uu____7018))::uu____7019
          -> bs
      | uu____7028 ->
          let uu____7029 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7029 with
           | None  -> bs
           | Some t ->
               let uu____7032 =
                 let uu____7033 = FStar_Syntax_Subst.compress t in
                 uu____7033.FStar_Syntax_Syntax.n in
               (match uu____7032 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7037) ->
                    let uu____7048 =
                      FStar_Util.prefix_until
                        (fun uu___104_7067  ->
                           match uu___104_7067 with
                           | (uu____7071,Some (FStar_Syntax_Syntax.Implicit
                              uu____7072)) -> false
                           | uu____7074 -> true) bs' in
                    (match uu____7048 with
                     | None  -> bs
                     | Some ([],uu____7092,uu____7093) -> bs
                     | Some (imps,uu____7130,uu____7131) ->
                         let uu____7168 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7176  ->
                                   match uu____7176 with
                                   | (x,uu____7181) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7168
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7204  ->
                                     match uu____7204 with
                                     | (x,i) ->
                                         let uu____7215 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7215, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7221 -> bs))
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
              (let uu____7240 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7240 e.FStar_Syntax_Syntax.pos)
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
          let uu____7262 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7262
          then e
          else
            (let uu____7264 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7264
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
        (let uu____7290 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7290
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7292 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7292))
         else ());
        (let fv =
           let uu____7295 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7295 None in
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
         let uu____7302 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___147_7311 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_7311.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_7311.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_7311.FStar_Syntax_Syntax.sigmeta)
           }), uu____7302))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7321 =
        match uu___105_7321 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7322 -> false in
      let reducibility uu___106_7326 =
        match uu___106_7326 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7327 -> false in
      let assumption uu___107_7331 =
        match uu___107_7331 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7332 -> false in
      let reification uu___108_7336 =
        match uu___108_7336 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7337 -> true
        | uu____7338 -> false in
      let inferred uu___109_7342 =
        match uu___109_7342 with
        | FStar_Syntax_Syntax.Discriminator uu____7343 -> true
        | FStar_Syntax_Syntax.Projector uu____7344 -> true
        | FStar_Syntax_Syntax.RecordType uu____7347 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7352 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7357 -> false in
      let has_eq uu___110_7361 =
        match uu___110_7361 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7362 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7396 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7399 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7402 =
        let uu____7403 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7405  ->
                  match uu___111_7405 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7406 -> false)) in
        FStar_All.pipe_right uu____7403 Prims.op_Negation in
      if uu____7402
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7416 =
            let uu____7417 =
              let uu____7420 =
                let uu____7421 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7421 msg in
              (uu____7420, r) in
            FStar_Errors.Error uu____7417 in
          raise uu____7416 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7429 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7437 =
            let uu____7438 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7438 in
          if uu____7437 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7442),uu____7443,uu____7444) ->
              ((let uu____7455 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7455
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7458 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7458
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7462 ->
              let uu____7467 =
                let uu____7468 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7468 in
              if uu____7467 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7472 ->
              let uu____7476 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7476 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7479 ->
              let uu____7483 =
                let uu____7484 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7484 in
              if uu____7483 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7488 ->
              let uu____7489 =
                let uu____7490 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7490 in
              if uu____7489 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7494 ->
              let uu____7495 =
                let uu____7496 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7496 in
              if uu____7495 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7500 ->
              let uu____7507 =
                let uu____7508 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7508 in
              if uu____7507 then err'1 () else ()
          | uu____7512 -> ()))
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
                          let uu____7569 =
                            let uu____7572 =
                              let uu____7573 =
                                let uu____7578 =
                                  let uu____7579 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7579 in
                                (uu____7578, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7573 in
                            FStar_Syntax_Syntax.mk uu____7572 in
                          uu____7569 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7605  ->
                                  match uu____7605 with
                                  | (x,imp) ->
                                      let uu____7612 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7612, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7616 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7616 in
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
                             let uu____7625 =
                               let uu____7626 =
                                 let uu____7627 =
                                   let uu____7628 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7629 =
                                     let uu____7630 =
                                       let uu____7631 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7631 in
                                     [uu____7630] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7628
                                     uu____7629 in
                                 uu____7627 None p in
                               FStar_Syntax_Util.b2t uu____7626 in
                             FStar_Syntax_Util.refine x uu____7625 in
                           let uu____7636 =
                             let uu___148_7637 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___148_7637.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___148_7637.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7636) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7647 =
                          FStar_List.map
                            (fun uu____7657  ->
                               match uu____7657 with
                               | (x,uu____7664) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7647 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7688  ->
                                match uu____7688 with
                                | (x,uu____7695) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7704 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7704)
                               ||
                               (let uu____7705 =
                                  let uu____7706 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7706.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7705) in
                           let quals =
                             let uu____7709 =
                               let uu____7711 =
                                 let uu____7713 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7713
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7716 =
                                 FStar_List.filter
                                   (fun uu___112_7718  ->
                                      match uu___112_7718 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7719 -> false) iquals in
                               FStar_List.append uu____7711 uu____7716 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7709 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7732 =
                                 let uu____7733 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7733 in
                               FStar_Syntax_Syntax.mk_Total uu____7732 in
                             let uu____7734 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7734 in
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
                           (let uu____7737 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7737
                            then
                              let uu____7738 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7738
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
                                             fun uu____7766  ->
                                               match uu____7766 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7782 =
                                                       let uu____7785 =
                                                         let uu____7786 =
                                                           let uu____7791 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7791,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7786 in
                                                       pos uu____7785 in
                                                     (uu____7782, b)
                                                   else
                                                     (let uu____7795 =
                                                        let uu____7798 =
                                                          let uu____7799 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7799 in
                                                        pos uu____7798 in
                                                      (uu____7795, b)))) in
                                   let pat_true =
                                     let uu____7811 =
                                       let uu____7814 =
                                         let uu____7815 =
                                           let uu____7823 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7823, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7815 in
                                       pos uu____7814 in
                                     (uu____7811, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7845 =
                                       let uu____7848 =
                                         let uu____7849 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7849 in
                                       pos uu____7848 in
                                     (uu____7845, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7858 =
                                     let uu____7861 =
                                       let uu____7862 =
                                         let uu____7878 =
                                           let uu____7880 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7881 =
                                             let uu____7883 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7883] in
                                           uu____7880 :: uu____7881 in
                                         (arg_exp, uu____7878) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7862 in
                                     FStar_Syntax_Syntax.mk uu____7861 in
                                   uu____7858 None p) in
                              let dd =
                                let uu____7894 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7894
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
                                let uu____7906 =
                                  let uu____7909 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7909 in
                                let uu____7910 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7906;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7910
                                } in
                              let impl =
                                let uu____7914 =
                                  let uu____7915 =
                                    let uu____7921 =
                                      let uu____7923 =
                                        let uu____7924 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7924
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7923] in
                                    ((false, [lb]), uu____7921, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7915 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7914;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7939 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7939
                               then
                                 let uu____7940 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7940
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
                                fun uu____7960  ->
                                  match uu____7960 with
                                  | (a,uu____7964) ->
                                      let uu____7965 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____7965 with
                                       | (field_name,uu____7969) ->
                                           let field_proj_tm =
                                             let uu____7971 =
                                               let uu____7972 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7972 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7971 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____7986 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7995  ->
                                    match uu____7995 with
                                    | (x,uu____8000) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8002 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8002 with
                                         | (field_name,uu____8007) ->
                                             let t =
                                               let uu____8009 =
                                                 let uu____8010 =
                                                   let uu____8013 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8013 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8010 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8009 in
                                             let only_decl =
                                               ((let uu____8015 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____8015)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8016 =
                                                    let uu____8017 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8017.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8016) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8027 =
                                                   FStar_List.filter
                                                     (fun uu___113_8029  ->
                                                        match uu___113_8029
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8030 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8027
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_8038  ->
                                                         match uu___114_8038
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8039 ->
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
                                             ((let uu____8042 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8042
                                               then
                                                 let uu____8043 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8043
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
                                                           fun uu____8070  ->
                                                             match uu____8070
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8086
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8086,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8098
                                                                    =
                                                                    let uu____8101
                                                                    =
                                                                    let uu____8102
                                                                    =
                                                                    let uu____8107
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8107,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8102 in
                                                                    pos
                                                                    uu____8101 in
                                                                    (uu____8098,
                                                                    b))
                                                                   else
                                                                    (let uu____8111
                                                                    =
                                                                    let uu____8114
                                                                    =
                                                                    let uu____8115
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8115 in
                                                                    pos
                                                                    uu____8114 in
                                                                    (uu____8111,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8127 =
                                                     let uu____8130 =
                                                       let uu____8131 =
                                                         let uu____8139 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8139,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8131 in
                                                     pos uu____8130 in
                                                   let uu____8145 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8127, None,
                                                     uu____8145) in
                                                 let body =
                                                   let uu____8156 =
                                                     let uu____8159 =
                                                       let uu____8160 =
                                                         let uu____8176 =
                                                           let uu____8178 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8178] in
                                                         (arg_exp,
                                                           uu____8176) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8160 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8159 in
                                                   uu____8156 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8195 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8195
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
                                                   let uu____8201 =
                                                     let uu____8204 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8204 in
                                                   let uu____8205 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8201;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8205
                                                   } in
                                                 let impl =
                                                   let uu____8209 =
                                                     let uu____8210 =
                                                       let uu____8216 =
                                                         let uu____8218 =
                                                           let uu____8219 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8219
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8218] in
                                                       ((false, [lb]),
                                                         uu____8216, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8210 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8209;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8234 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8234
                                                  then
                                                    let uu____8235 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8235
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____7986 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8265) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8268 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8268 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8281 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8281 with
                    | (formals,uu____8291) ->
                        let uu____8302 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8315 =
                                   let uu____8316 =
                                     let uu____8317 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8317 in
                                   FStar_Ident.lid_equals typ_lid uu____8316 in
                                 if uu____8315
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8327,uvs',tps,typ0,uu____8331,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8344 -> failwith "Impossible"
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
                        (match uu____8302 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8386 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8386 with
                              | (indices,uu____8396) ->
                                  let refine_domain =
                                    let uu____8408 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8410  ->
                                              match uu___115_8410 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8411 -> true
                                              | uu____8416 -> false)) in
                                    if uu____8408
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8423 =
                                      match uu___116_8423 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8425,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8432 -> None in
                                    let uu____8433 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8433 with
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
                                    let uu____8441 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8441 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8472  ->
                                               fun uu____8473  ->
                                                 match (uu____8472,
                                                         uu____8473)
                                                 with
                                                 | ((x,uu____8483),(x',uu____8485))
                                                     ->
                                                     let uu____8490 =
                                                       let uu____8495 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8495) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8490) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8496 -> []