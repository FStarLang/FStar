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
              (fun uu____254  ->
                 match uu____254 with
                 | (x,uu____262) -> FStar_Syntax_Print.uvar_to_string x)
              uu____238 in
          FStar_All.pipe_right uu____236 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____279 =
            let uu____280 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____280 in
          FStar_Errors.err r uu____279);
         FStar_Options.pop ())
      else ()
let force_sort':
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____289 = FStar_ST.read s.FStar_Syntax_Syntax.tk in
    match uu____289 with
    | None  ->
        let uu____294 =
          let uu____295 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos in
          let uu____296 = FStar_Syntax_Print.term_to_string s in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____295 uu____296 in
        failwith uu____294
    | Some tk -> tk
let force_sort s =
  let uu____311 =
    let uu____314 = force_sort' s in FStar_Syntax_Syntax.mk uu____314 in
  uu____311 None s.FStar_Syntax_Syntax.pos
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.typ*
        Prims.bool)
  =
  fun env  ->
    fun uu____331  ->
      match uu____331 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____338;
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
                   let uu____370 =
                     let uu____371 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____371.FStar_Syntax_Syntax.n in
                   match uu____370 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____376 = FStar_Syntax_Util.type_u () in
                       (match uu____376 with
                        | (k,uu____382) ->
                            let t2 =
                              let uu____384 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____384
                                FStar_Pervasives.fst in
                            ((let uu___118_389 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_389.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_389.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____390 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____415) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____422) ->
                       ((fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____468) ->
                       let uu____491 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____515  ->
                                 fun uu____516  ->
                                   match (uu____515, uu____516) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____558 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____558 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____491 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____619 = aux must_check_ty1 scope body in
                            (match uu____619 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____636 =
                                         FStar_Options.ml_ish () in
                                       if uu____636
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____643 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____643
                                   then
                                     let uu____644 =
                                       FStar_Range.string_of_range r in
                                     let uu____645 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____646 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____644 uu____645 uu____646
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____654 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____662 =
                            let uu____665 =
                              let uu____666 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____666
                                FStar_Pervasives.fst in
                            FStar_Util.Inl uu____665 in
                          (uu____662, false)) in
                 let uu____673 =
                   let uu____678 = t_binders env in aux false uu____678 e in
                 match uu____673 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____695 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____695
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____699 =
                                let uu____700 =
                                  let uu____703 =
                                    let uu____704 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____704 in
                                  (uu____703, rng) in
                                FStar_Errors.Error uu____700 in
                              raise uu____699)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____711 ->
               let uu____712 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____712 with
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
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____795) ->
              let uu____800 = FStar_Syntax_Util.type_u () in
              (match uu____800 with
               | (k,uu____813) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___119_816 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___119_816.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___119_816.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____817 =
                     let uu____820 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____820 t in
                   (match uu____817 with
                    | (e,u) ->
                        let p2 =
                          let uu___120_835 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___120_835.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___120_835.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____842 = FStar_Syntax_Util.type_u () in
              (match uu____842 with
               | (t,uu____855) ->
                   let x1 =
                     let uu___121_857 = x in
                     let uu____858 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___121_857.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___121_857.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____858
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
              let uu____880 = FStar_Syntax_Util.type_u () in
              (match uu____880 with
               | (t,uu____893) ->
                   let x1 =
                     let uu___122_895 = x in
                     let uu____896 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___122_895.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___122_895.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____896
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____928 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____984  ->
                        fun uu____985  ->
                          match (uu____984, uu____985) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1084 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1084 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____928 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1192 =
                       let uu____1195 =
                         let uu____1196 =
                           let uu____1201 =
                             let uu____1204 =
                               let uu____1205 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1206 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1205
                                 uu____1206 in
                             uu____1204 None p1.FStar_Syntax_Syntax.p in
                           (uu____1201,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1196 in
                       FStar_Syntax_Syntax.mk uu____1195 in
                     uu____1192 None p1.FStar_Syntax_Syntax.p in
                   let uu____1223 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1229 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1235 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1223, uu____1229, uu____1235, env2, e,
                     (let uu___123_1248 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___123_1248.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___123_1248.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1254 -> failwith "impossible" in
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
                  (fun uu____1323  ->
                     match uu____1323 with
                     | (p2,imp) ->
                         let uu____1338 = elaborate_pat env1 p2 in
                         (uu____1338, imp)) pats in
              let uu____1343 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____1343 with
               | (uu____1352,t) ->
                   let uu____1354 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____1354 with
                    | (f,uu____1365) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1440::uu____1441) ->
                              raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1476::uu____1477,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1517  ->
                                      match uu____1517 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1535 =
                                                   let uu____1537 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   Some uu____1537 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1535
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____1543 =
                                                 maybe_dot inaccessible a r in
                                               (uu____1543, true)
                                           | uu____1548 ->
                                               let uu____1550 =
                                                 let uu____1551 =
                                                   let uu____1554 =
                                                     let uu____1555 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1555 in
                                                   (uu____1554,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____1551 in
                                               raise uu____1550)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1606,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1607))
                                   when p_imp ->
                                   let uu____1609 = aux formals' pats' in
                                   (p2, true) :: uu____1609
                               | (uu____1621,Some
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
                                   let uu____1632 = aux formals' pats2 in
                                   (p3, true) :: uu____1632
                               | (uu____1644,imp) ->
                                   let uu____1648 =
                                     let uu____1653 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____1653) in
                                   let uu____1656 = aux formals' pats' in
                                   uu____1648 :: uu____1656) in
                        let uu___124_1666 = p1 in
                        let uu____1669 =
                          let uu____1670 =
                            let uu____1678 = aux f pats1 in (fv, uu____1678) in
                          FStar_Syntax_Syntax.Pat_cons uu____1670 in
                        {
                          FStar_Syntax_Syntax.v = uu____1669;
                          FStar_Syntax_Syntax.ty =
                            (uu___124_1666.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___124_1666.FStar_Syntax_Syntax.p)
                        }))
          | uu____1689 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1715 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____1715 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1745 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1745 with
               | Some x ->
                   let uu____1758 =
                     let uu____1759 =
                       let uu____1762 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____1762, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____1759 in
                   raise uu____1758
               | uu____1771 -> (b, a, w, arg, p3)) in
        let top_level_pat_as_args env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1814 = one_pat false env1 q in
              (match uu____1814 with
               | (b,a,uu____1830,te,q1) ->
                   let uu____1839 =
                     FStar_List.fold_right
                       (fun p2  ->
                          fun uu____1855  ->
                            match uu____1855 with
                            | (w,args,pats1) ->
                                let uu____1879 = one_pat false env1 p2 in
                                (match uu____1879 with
                                 | (b',a',w',arg,p3) ->
                                     let uu____1905 =
                                       let uu____1906 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a' in
                                       Prims.op_Negation uu____1906 in
                                     if uu____1905
                                     then
                                       let uu____1913 =
                                         let uu____1914 =
                                           let uu____1917 =
                                             FStar_TypeChecker_Err.disjunctive_pattern_vars
                                               a a' in
                                           let uu____1918 =
                                             FStar_TypeChecker_Env.get_range
                                               env1 in
                                           (uu____1917, uu____1918) in
                                         FStar_Errors.Error uu____1914 in
                                       raise uu____1913
                                     else
                                       (let uu____1926 =
                                          let uu____1928 =
                                            FStar_Syntax_Syntax.as_arg arg in
                                          uu____1928 :: args in
                                        ((FStar_List.append w' w),
                                          uu____1926, (p3 :: pats1))))) pats
                       ([], [], []) in
                   (match uu____1839 with
                    | (w,args,pats1) ->
                        let uu____1949 =
                          let uu____1951 = FStar_Syntax_Syntax.as_arg te in
                          uu____1951 :: args in
                        ((FStar_List.append b w), uu____1949,
                          (let uu___125_1956 = p1 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___125_1956.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___125_1956.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1957 ->
              let uu____1958 = one_pat true env1 p1 in
              (match uu____1958 with
               | (b,uu____1973,uu____1974,arg,p2) ->
                   let uu____1983 =
                     let uu____1985 = FStar_Syntax_Syntax.as_arg arg in
                     [uu____1985] in
                   (b, uu____1983, p2)) in
        let uu____1988 = top_level_pat_as_args env p in
        match uu____1988 with
        | (b,args,p1) ->
            let exps =
              FStar_All.pipe_right args (FStar_List.map FStar_Pervasives.fst) in
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
          | (uu____2059,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2061)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2066,FStar_Syntax_Syntax.Tm_constant uu____2067) ->
              let uu____2068 = force_sort' e1 in
              pkg p1.FStar_Syntax_Syntax.v uu____2068
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2072 =
                    let uu____2073 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2074 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2073 uu____2074 in
                  failwith uu____2072)
               else ();
               (let uu____2077 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2077
                then
                  let uu____2078 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2079 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2078
                    uu____2079
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___126_2083 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_2083.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_2083.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2087 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2087
                then
                  let uu____2088 =
                    let uu____2089 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2090 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2089 uu____2090 in
                  failwith uu____2088
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___127_2094 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_2094.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_2094.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2096),uu____2097) ->
              let s = force_sort e1 in
              let x1 =
                let uu___128_2106 = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___128_2106.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___128_2106.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                } in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2119 =
                  let uu____2120 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2120 in
                if uu____2119
                then
                  let uu____2121 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2121
                else ());
               (let uu____2131 = force_sort' e1 in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2131))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = uu____2144;
                FStar_Syntax_Syntax.pos = uu____2145;
                FStar_Syntax_Syntax.vars = uu____2146;_},args))
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
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.tk = uu____2401;
                     FStar_Syntax_Syntax.pos = uu____2402;
                     FStar_Syntax_Syntax.vars = uu____2403;_},uu____2404);
                FStar_Syntax_Syntax.tk = uu____2405;
                FStar_Syntax_Syntax.pos = uu____2406;
                FStar_Syntax_Syntax.vars = uu____2407;_},args))
              ->
              ((let uu____2438 =
                  let uu____2439 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2439 Prims.op_Negation in
                if uu____2438
                then
                  let uu____2440 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2440
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2528 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2528
                  | (arg::args2,(argpat,uu____2541)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2591) ->
                           let x =
                             let uu____2607 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2607 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2621) ->
                           let pat =
                             let uu____2636 = aux argpat e2 in
                             let uu____2637 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2636, uu____2637) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2640 ->
                      let uu____2654 =
                        let uu____2655 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2656 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2655 uu____2656 in
                      failwith uu____2654 in
                match_args [] args argpats))
          | uu____2663 ->
              let uu____2666 =
                let uu____2667 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2668 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2669 =
                  let uu____2670 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string) in
                  FStar_All.pipe_right uu____2670
                    (FStar_String.concat "\n\t") in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2667 uu____2668 uu____2669 in
              failwith uu____2666 in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2677) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2693,e::[]) -> aux p e
        | uu____2696 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2733 =
      match uu____2733 with
      | (p,i) ->
          let uu____2743 = decorated_pattern_as_term p in
          (match uu____2743 with
           | (vars,te) ->
               let uu____2756 =
                 let uu____2759 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2759) in
               (vars, uu____2756)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2766 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2774 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2774)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____2777 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2777)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____2780 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2780)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2794 =
          let uu____2802 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2802 FStar_List.unzip in
        (match uu____2794 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2860 =
               let uu____2861 =
                 let uu____2862 =
                   let uu____2872 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2872, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2862 in
               mk1 uu____2861 in
             (vars1, uu____2860))
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
      | (wp,uu____2901)::[] -> wp
      | uu____2914 ->
          let uu____2920 =
            let uu____2921 =
              let uu____2922 =
                FStar_List.map
                  (fun uu____2926  ->
                     match uu____2926 with
                     | (x,uu____2930) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2922 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2921 in
          failwith uu____2920 in
    let uu____2934 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2934, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2948 = destruct_comp c in
        match uu____2948 with
        | (u,uu____2953,wp) ->
            let uu____2955 =
              let uu____2961 =
                let uu____2962 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2962 in
              [uu____2961] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2955;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2972 =
          let uu____2976 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2977 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2976 uu____2977 in
        match uu____2972 with | (m,uu____2979,uu____2980) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2990 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2990
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
        let uu____3015 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____3015 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____3037 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____3037 with
             | (a,kwp) ->
                 let uu____3054 = destruct_comp m1 in
                 let uu____3058 = destruct_comp m2 in
                 ((md, a, kwp), uu____3054, uu____3058))
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
            let uu____3106 =
              let uu____3107 =
                let uu____3113 = FStar_Syntax_Syntax.as_arg wp in
                [uu____3113] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____3107;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____3106
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
      let uu___129_3149 = lc in
      let uu____3150 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___129_3149.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____3150;
        FStar_Syntax_Syntax.cflags =
          (uu___129_3149.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____3153  ->
             let uu____3154 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____3154)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3158 =
      let uu____3159 = FStar_Syntax_Subst.compress t in
      uu____3159.FStar_Syntax_Syntax.n in
    match uu____3158 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3162 -> true
    | uu____3170 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3182 = FStar_Syntax_Util.is_ml_comp c in
        if uu____3182
        then c
        else
          (let uu____3184 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____3184
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3214 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____3214] in
                       let us =
                         let uu____3217 =
                           let uu____3219 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____3219] in
                         u_res :: uu____3217 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____3230 =
                         let uu____3231 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____3232 =
                           let uu____3233 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____3234 =
                             let uu____3236 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____3237 =
                               let uu____3239 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____3239] in
                             uu____3236 :: uu____3237 in
                           uu____3233 :: uu____3234 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3231 uu____3232 in
                       uu____3230 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____3245 = destruct_comp c1 in
              match uu____3245 with
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
        let close1 uu____3268 =
          let uu____3269 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____3269 in
        let uu___130_3270 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___130_3270.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___130_3270.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___130_3270.FStar_Syntax_Syntax.cflags);
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
          let uu____3281 =
            let uu____3282 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____3282 in
          if uu____3281
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____3287 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____3287
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____3289 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____3289 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____3295 =
                        let uu____3296 =
                          let uu____3297 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3298 =
                            let uu____3299 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3300 =
                              let uu____3302 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3302] in
                            uu____3299 :: uu____3300 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3297 uu____3298 in
                        uu____3296 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____3295) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3308 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3308
         then
           let uu____3309 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3310 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3311 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3309
             uu____3310 uu____3311
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
          fun uu____3328  ->
            match uu____3328 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3338 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3338
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3341 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3343 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3344 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3341 uu____3343 bstr uu____3344
                  else ());
                 (let bind_it uu____3349 =
                    let uu____3350 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3350
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3360 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3360
                        then
                          let uu____3361 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3363 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3364 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3365 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3366 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3361 uu____3363 uu____3364 uu____3365
                            uu____3366
                        else ());
                       (let try_simplify uu____3377 =
                          let aux uu____3387 =
                            let uu____3388 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3388
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3407 ->
                                  let uu____3408 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3408
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3427 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3427
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3463 =
                                  let uu____3466 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3466, reason) in
                                FStar_Util.Inl uu____3463
                            | uu____3469 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3484 =
                              let uu____3485 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3485.FStar_Syntax_Syntax.n in
                            match uu____3484 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3489) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3495 -> c in
                          let uu____3496 =
                            let uu____3497 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3497 in
                          if uu____3496
                          then
                            let uu____3505 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3505
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3519 =
                                  let uu____3520 =
                                    let uu____3523 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3523) in
                                  FStar_Errors.Error uu____3520 in
                                raise uu____3519))
                          else
                            (let uu____3531 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3531
                             then subst_c2 "both total"
                             else
                               (let uu____3539 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3539
                                then
                                  let uu____3546 =
                                    let uu____3549 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3549, "both gtot") in
                                  FStar_Util.Inl uu____3546
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3565 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3566 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3566) in
                                       if uu____3565
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___131_3575 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___131_3575.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___131_3575.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3576 =
                                           let uu____3579 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3579, "c1 Tot") in
                                         FStar_Util.Inl uu____3576
                                       else aux ()
                                   | uu____3583 -> aux ()))) in
                        let uu____3588 = try_simplify () in
                        match uu____3588 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3606 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3606
                              then
                                let uu____3607 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3608 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3609 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3607 uu____3608 uu____3609
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3616 = lift_and_destruct env c1 c2 in
                            (match uu____3616 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3650 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3650]
                                   | Some x ->
                                       let uu____3652 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3652] in
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
                                   let uu____3675 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3676 =
                                     let uu____3678 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3679 =
                                       let uu____3681 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3682 =
                                         let uu____3684 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3685 =
                                           let uu____3687 =
                                             let uu____3688 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3688 in
                                           [uu____3687] in
                                         uu____3684 :: uu____3685 in
                                       uu____3681 :: uu____3682 in
                                     uu____3678 :: uu____3679 in
                                   uu____3675 :: uu____3676 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3693 =
                                     let uu____3694 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3694
                                       wp_args in
                                   uu____3693 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3738 =
                let uu____3739 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3739 in
              if uu____3738
              then f
              else (let uu____3741 = reason1 () in label uu____3741 r f)
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
            let uu___132_3752 = g in
            let uu____3753 =
              let uu____3754 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3754 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3753;
              FStar_TypeChecker_Env.deferred =
                (uu___132_3752.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_3752.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_3752.FStar_TypeChecker_Env.implicits)
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
      | uu____3766 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3783 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3787 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3787
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3794 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3794
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3799 = destruct_comp c1 in
                    match uu____3799 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3812 =
                            let uu____3813 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3814 =
                              let uu____3815 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3816 =
                                let uu____3818 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3819 =
                                  let uu____3821 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3821] in
                                uu____3818 :: uu____3819 in
                              uu____3815 :: uu____3816 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3813
                              uu____3814 in
                          uu____3812 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___133_3826 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___133_3826.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___133_3826.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___133_3826.FStar_Syntax_Syntax.cflags);
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
            let uu____3853 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3853
            then (lc, g0)
            else
              ((let uu____3858 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3858
                then
                  let uu____3859 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3860 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3859 uu____3860
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3866  ->
                          match uu___98_3866 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3868 -> [])) in
                let strengthen uu____3874 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3882 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3882 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3889 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3890 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3890) in
                           if uu____3889
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3897 =
                                 let uu____3898 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3898 in
                               FStar_Syntax_Util.comp_set_flags uu____3897
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3903 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3903
                           then
                             let uu____3904 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3905 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3904 uu____3905
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3908 = destruct_comp c2 in
                           match uu____3908 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3921 =
                                   let uu____3922 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3923 =
                                     let uu____3924 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3925 =
                                       let uu____3927 =
                                         let uu____3928 =
                                           let uu____3929 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3929 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3928 in
                                       let uu____3930 =
                                         let uu____3932 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3932] in
                                       uu____3927 :: uu____3930 in
                                     uu____3924 :: uu____3925 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3922
                                     uu____3923 in
                                 uu____3921 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3938 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3938
                                 then
                                   let uu____3939 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3939
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3942 =
                  let uu___134_3943 = lc in
                  let uu____3944 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3945 =
                    let uu____3947 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3948 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3948) in
                    if uu____3947 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3944;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___134_3943.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3945;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3942,
                  (let uu___135_3951 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___135_3951.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___135_3951.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___135_3951.FStar_TypeChecker_Env.implicits)
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
        let uu____3966 =
          let uu____3969 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3970 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3969, uu____3970) in
        match uu____3966 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3979 =
                let uu____3980 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3981 =
                  let uu____3982 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3983 =
                    let uu____3985 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3985] in
                  uu____3982 :: uu____3983 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3980 uu____3981 in
              uu____3979 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3993 =
                let uu____3994 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3995 =
                  let uu____3996 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3997 =
                    let uu____3999 =
                      let uu____4000 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____4000 in
                    let uu____4001 =
                      let uu____4003 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____4003] in
                    uu____3999 :: uu____4001 in
                  uu____3996 :: uu____3997 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3994 uu____3995 in
              uu____3993 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____4011 =
                let uu____4012 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____4013 =
                  let uu____4014 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____4015 =
                    let uu____4017 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____4018 =
                      let uu____4020 =
                        let uu____4021 =
                          let uu____4022 =
                            let uu____4023 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____4023] in
                          FStar_Syntax_Util.abs uu____4022 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____4021 in
                      [uu____4020] in
                    uu____4017 :: uu____4018 in
                  uu____4014 :: uu____4015 in
                FStar_Syntax_Syntax.mk_Tm_app uu____4012 uu____4013 in
              uu____4011 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____4039 = FStar_TypeChecker_Env.get_range env in
              bind uu____4039 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____4057 =
            let uu____4058 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____4058
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____4061 =
                 let uu____4074 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____4075 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____4074 uu____4075 in
               match uu____4061 with
               | ((md,uu____4077,uu____4078),(u_res_t,res_t,wp_then),
                  (uu____4082,uu____4083,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____4112 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____4113 =
                       let uu____4114 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____4115 =
                         let uu____4116 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____4117 =
                           let uu____4119 = FStar_Syntax_Syntax.as_arg g in
                           let uu____4120 =
                             let uu____4122 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____4123 =
                               let uu____4125 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____4125] in
                             uu____4122 :: uu____4123 in
                           uu____4119 :: uu____4120 in
                         uu____4116 :: uu____4117 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4114 uu____4115 in
                     uu____4113 None uu____4112 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____4133 =
                     let uu____4134 = FStar_Options.split_cases () in
                     uu____4134 > (Prims.parse_int "0") in
                   if uu____4133
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____4140 =
                          let uu____4141 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____4142 =
                            let uu____4143 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____4144 =
                              let uu____4146 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____4146] in
                            uu____4143 :: uu____4144 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4141 uu____4142 in
                        uu____4140 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____4151 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____4151;
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
      let uu____4158 =
        let uu____4159 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____4159 in
      FStar_Syntax_Syntax.fvar uu____4158 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____4179  ->
                 match uu____4179 with
                 | (uu____4182,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____4187 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____4189 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____4189
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____4209 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____4210 =
                 let uu____4211 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____4212 =
                   let uu____4213 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____4214 =
                     let uu____4216 = FStar_Syntax_Syntax.as_arg g in
                     let uu____4217 =
                       let uu____4219 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____4220 =
                         let uu____4222 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____4222] in
                       uu____4219 :: uu____4220 in
                     uu____4216 :: uu____4217 in
                   uu____4213 :: uu____4214 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4211 uu____4212 in
               uu____4210 None uu____4209 in
             let default_case =
               let post_k =
                 let uu____4231 =
                   let uu____4235 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____4235] in
                 let uu____4236 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4231 uu____4236 in
               let kwp =
                 let uu____4242 =
                   let uu____4246 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____4246] in
                 let uu____4247 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4242 uu____4247 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____4252 =
                   let uu____4253 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____4253] in
                 let uu____4254 =
                   let uu____4255 =
                     let uu____4258 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____4258 in
                   let uu____4259 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____4255 uu____4259 in
                 FStar_Syntax_Util.abs uu____4252 uu____4254
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
                 (fun uu____4273  ->
                    fun celse  ->
                      match uu____4273 with
                      | (g,cthen) ->
                          let uu____4279 =
                            let uu____4292 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____4292 celse in
                          (match uu____4279 with
                           | ((md,uu____4294,uu____4295),(uu____4296,uu____4297,wp_then),
                              (uu____4299,uu____4300,wp_else)) ->
                               let uu____4311 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4311 []))
                 lcases default_case in
             let uu____4312 =
               let uu____4313 = FStar_Options.split_cases () in
               uu____4313 > (Prims.parse_int "0") in
             if uu____4312
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4317 = destruct_comp comp1 in
                match uu____4317 with
                | (uu____4321,uu____4322,wp) ->
                    let wp1 =
                      let uu____4327 =
                        let uu____4328 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4329 =
                          let uu____4330 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4331 =
                            let uu____4333 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4333] in
                          uu____4330 :: uu____4331 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4328 uu____4329 in
                      uu____4327 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4349 =
            ((let uu____4350 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4350) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4351 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4351) in
          if uu____4349
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4359 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4363 =
            (let uu____4364 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4364) || env.FStar_TypeChecker_Env.lax in
          if uu____4363
          then c
          else
            (let uu____4368 = FStar_Syntax_Util.is_partial_return c in
             if uu____4368
             then c
             else
               (let uu____4372 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4372
                then
                  let uu____4375 =
                    let uu____4376 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4376 in
                  (if uu____4375
                   then
                     let uu____4379 =
                       let uu____4380 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4381 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4380 uu____4381 in
                     failwith uu____4379
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4386 =
                        let uu____4387 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4387 in
                      if uu____4386
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___136_4392 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___136_4392.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___136_4392.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___136_4392.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4403 =
                       let uu____4406 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4406
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4403 in
                   let eq1 =
                     let uu____4410 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4410 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4412 =
                     let uu____4413 =
                       let uu____4418 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4418.FStar_Syntax_Syntax.comp in
                     uu____4413 () in
                   FStar_Syntax_Util.comp_set_flags uu____4412 flags))) in
        let uu___137_4420 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4420.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4420.FStar_Syntax_Syntax.res_typ);
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
          let uu____4439 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4439 with
          | None  ->
              let uu____4444 =
                let uu____4445 =
                  let uu____4448 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4449 = FStar_TypeChecker_Env.get_range env in
                  (uu____4448, uu____4449) in
                FStar_Errors.Error uu____4445 in
              raise uu____4444
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
            let uu____4475 =
              let uu____4476 = FStar_Syntax_Subst.compress t2 in
              uu____4476.FStar_Syntax_Syntax.n in
            match uu____4475 with
            | FStar_Syntax_Syntax.Tm_type uu____4479 -> true
            | uu____4480 -> false in
          let uu____4481 =
            let uu____4482 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4482.FStar_Syntax_Syntax.n in
          match uu____4481 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4488 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4495 =
                  let uu____4496 =
                    let uu____4497 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4497 in
                  (None, uu____4496) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4495 in
              let e1 =
                let uu____4506 =
                  let uu____4507 =
                    let uu____4508 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4508] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4507 in
                uu____4506
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4515 -> (e, lc)
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
              (let uu____4535 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4535 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4548 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4560 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4560, false)
            else
              (let uu____4564 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4564, true)) in
          match gopt with
          | (None ,uu____4570) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___138_4573 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___138_4573.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___138_4573.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___138_4573.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4577 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4577 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___139_4582 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_4582.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_4582.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___139_4582.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___140_4585 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___140_4585.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___140_4585.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___140_4585.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4591 =
                     let uu____4592 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4592
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4597 =
                          let uu____4598 = FStar_Syntax_Subst.compress f1 in
                          uu____4598.FStar_Syntax_Syntax.n in
                        match uu____4597 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4603,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4605;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4606;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4607;_},uu____4608)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___141_4632 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___141_4632.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___141_4632.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___141_4632.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4633 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4638 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4638
                              then
                                let uu____4639 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4640 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4641 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4642 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4639 uu____4640 uu____4641 uu____4642
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4645 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4645 with
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
                                  let uu____4656 = destruct_comp ct in
                                  (match uu____4656 with
                                   | (u_t,uu____4663,uu____4664) ->
                                       let wp =
                                         let uu____4668 =
                                           let uu____4669 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4670 =
                                             let uu____4671 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4672 =
                                               let uu____4674 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4674] in
                                             uu____4671 :: uu____4672 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4669 uu____4670 in
                                         uu____4668
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4680 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4680 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4690 =
                                             let uu____4691 =
                                               let uu____4692 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4692] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4691 in
                                           uu____4690
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4698 =
                                         let uu____4701 =
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4712 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4713 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4701
                                           uu____4712 e cret uu____4713 in
                                       (match uu____4698 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___142_4719 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___142_4719.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___142_4719.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4721 =
                                                let uu____4722 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4722 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4721
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4732 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4732
                                              then
                                                let uu____4733 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4733
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4739  ->
                             match uu___99_4739 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4741 -> [])) in
                   let lc1 =
                     let uu___143_4743 = lc in
                     let uu____4744 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4744;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___144_4746 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_4746.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_4746.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_4746.FStar_TypeChecker_Env.implicits)
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
        let uu____4766 =
          let uu____4767 =
            let uu____4768 =
              let uu____4769 =
                let uu____4770 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4770 in
              [uu____4769] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4768 in
          uu____4767 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4766 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4779 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4779
      then (None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4790 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4799 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4816)::(ens,uu____4818)::uu____4819 ->
                    let uu____4841 =
                      let uu____4843 = norm req in Some uu____4843 in
                    let uu____4844 =
                      let uu____4845 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4845 in
                    (uu____4841, uu____4844)
                | uu____4847 ->
                    let uu____4853 =
                      let uu____4854 =
                        let uu____4857 =
                          let uu____4858 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4858 in
                        (uu____4857, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4854 in
                    raise uu____4853)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4868)::uu____4869 ->
                    let uu____4883 =
                      let uu____4886 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4886 in
                    (match uu____4883 with
                     | (us_r,uu____4903) ->
                         let uu____4904 =
                           let uu____4907 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4907 in
                         (match uu____4904 with
                          | (us_e,uu____4924) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4927 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4927
                                  us_r in
                              let as_ens =
                                let uu____4929 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4929
                                  us_e in
                              let req =
                                let uu____4933 =
                                  let uu____4934 =
                                    let uu____4935 =
                                      let uu____4942 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4942] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4935 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4934 in
                                uu____4933
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4958 =
                                  let uu____4959 =
                                    let uu____4960 =
                                      let uu____4967 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4967] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4960 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4959 in
                                uu____4958 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4980 =
                                let uu____4982 = norm req in Some uu____4982 in
                              let uu____4983 =
                                let uu____4984 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4984 in
                              (uu____4980, uu____4983)))
                | uu____4986 -> failwith "Impossible"))
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
      (let uu____5006 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____5006
       then
         let uu____5007 = FStar_Syntax_Print.term_to_string tm in
         let uu____5008 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5007 uu____5008
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
        (let uu____5029 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____5029
         then
           let uu____5030 = FStar_Syntax_Print.term_to_string tm in
           let uu____5031 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____5030
             uu____5031
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____5036 =
      let uu____5037 =
        let uu____5038 = FStar_Syntax_Subst.compress t in
        uu____5038.FStar_Syntax_Syntax.n in
      match uu____5037 with
      | FStar_Syntax_Syntax.Tm_app uu____5041 -> false
      | uu____5051 -> true in
    if uu____5036
    then t
    else
      (let uu____5053 = FStar_Syntax_Util.head_and_args t in
       match uu____5053 with
       | (head1,args) ->
           let uu____5079 =
             let uu____5080 =
               let uu____5081 = FStar_Syntax_Subst.compress head1 in
               uu____5081.FStar_Syntax_Syntax.n in
             match uu____5080 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____5084 -> false in
           if uu____5079
           then
             (match args with
              | x::[] -> fst x
              | uu____5100 ->
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
             let uu____5128 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____5128 with
             | (formals,uu____5137) ->
                 let n_implicits =
                   let uu____5149 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____5186  ->
                             match uu____5186 with
                             | (uu____5190,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____5149 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____5262 = FStar_TypeChecker_Env.expected_typ env in
             match uu____5262 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____5276 =
                     let uu____5277 =
                       let uu____5280 =
                         let uu____5281 = FStar_Util.string_of_int n_expected in
                         let uu____5285 = FStar_Syntax_Print.term_to_string e in
                         let uu____5286 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____5281 uu____5285 uu____5286 in
                       let uu____5290 = FStar_TypeChecker_Env.get_range env in
                       (uu____5280, uu____5290) in
                     FStar_Errors.Error uu____5277 in
                   raise uu____5276
                 else Some (n_available - n_expected) in
           let decr_inst uu___100_5303 =
             match uu___100_5303 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5322 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5322 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_30,uu____5383) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5405,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5424 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5424 with
                           | (v1,uu____5445,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5455 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5455 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5504 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5504)))
                      | (uu____5518,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5542 =
                      let uu____5556 = inst_n_binders t in
                      aux [] uu____5556 bs1 in
                    (match uu____5542 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5594) -> (e, torig, guard)
                          | (uu____5610,[]) when
                              let uu____5626 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5626 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5627 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5646 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5661 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____5673 =
    let uu____5675 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5675
      (FStar_List.map
         (fun u  ->
            let uu____5685 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5685 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5673 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5697 = FStar_Util.set_is_empty x in
      if uu____5697
      then []
      else
        (let s =
           let uu____5702 =
             let uu____5704 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5704 in
           FStar_All.pipe_right uu____5702 FStar_Util.set_elements in
         (let uu____5709 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5709
          then
            let uu____5710 =
              let uu____5711 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5711 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5710
          else ());
         (let r =
            let uu____5719 = FStar_TypeChecker_Env.get_range env in
            Some uu____5719 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5731 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5731
                     then
                       let uu____5732 =
                         let uu____5733 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5733 in
                       let uu____5735 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5736 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5732 uu____5735 uu____5736
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
        let uu____5754 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5754 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5781 =
  match uu___101_5781 with
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
        | ([],uu____5822) -> generalized_univ_names
        | (uu____5826,[]) -> explicit_univ_names
        | uu____5830 ->
            let uu____5835 =
              let uu____5836 =
                let uu____5839 =
                  let uu____5840 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5840 in
                (uu____5839, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5836 in
            raise uu____5835
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
      (let uu____5854 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5854
       then
         let uu____5855 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5855
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5861 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5861
        then
          let uu____5862 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5862
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5867 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5867))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5897 =
        let uu____5898 =
          FStar_Util.for_all
            (fun uu____5903  ->
               match uu____5903 with
               | (uu____5908,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5898 in
      if uu____5897
      then None
      else
        (let norm c =
           (let uu____5931 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5931
            then
              let uu____5932 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5932
            else ());
           (let c1 =
              let uu____5935 = FStar_TypeChecker_Env.should_verify env in
              if uu____5935
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5938 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5938
             then
               let uu____5939 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5939
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5973 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5973 FStar_Util.set_elements in
         let uu____6017 =
           let uu____6035 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____6090  ->
                     match uu____6090 with
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
           FStar_All.pipe_right uu____6035 FStar_List.unzip in
         match uu____6017 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6252 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6252
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
                      (fun uu____6294  ->
                         match uu____6294 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6351  ->
                                       match uu____6351 with
                                       | (u,k) ->
                                           let uu____6371 =
                                             FStar_Unionfind.find u in
                                           (match uu____6371 with
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_name
                                                    a;
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6382;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6383;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6384;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (uu____6390,{
                                                                  FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_name
                                                                    a;
                                                                  FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____6392;
                                                                  FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____6393;
                                                                  FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____6394;_},uu____6395);
                                                  FStar_Syntax_Syntax.tk =
                                                    uu____6396;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____6397;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____6398;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____6426 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6434 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6439 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6439 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6463 =
                                                         let uu____6465 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              Some _0_31)
                                                           uu____6465 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6463 kres in
                                                     let t =
                                                       let uu____6468 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6469 =
                                                         let uu____6476 =
                                                           let uu____6482 =
                                                             let uu____6483 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6483 in
                                                           FStar_Util.Inl
                                                             uu____6482 in
                                                         Some uu____6476 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6468
                                                         uu____6469 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6498 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6516 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6516, c)
                               | ([],uu____6517) ->
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
                               | uu____6529 ->
                                   let uu____6537 = (e, c) in
                                   (match uu____6537 with
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
                                          let uu____6549 =
                                            let uu____6550 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6550.FStar_Syntax_Syntax.n in
                                          match uu____6549 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6567 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6567 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6577 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6587 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6587)) in
                             (match uu____6498 with
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
      (let uu____6625 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6625
       then
         let uu____6626 =
           let uu____6627 =
             FStar_List.map
               (fun uu____6632  ->
                  match uu____6632 with
                  | (lb,uu____6637,uu____6638) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6627 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6626
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6648  ->
              match uu____6648 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6663 =
           let uu____6670 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6686  ->
                     match uu____6686 with | (uu____6692,e,c) -> (e, c))) in
           gen env uu____6670 in
         match uu____6663 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6724  ->
                     match uu____6724 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6768  ->
                  fun uu____6769  ->
                    match (uu____6768, uu____6769) with
                    | ((l,uu____6802,uu____6803),(us,e,c)) ->
                        ((let uu____6829 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6829
                          then
                            let uu____6830 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6831 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6832 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6833 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6830 uu____6831 uu____6832 uu____6833
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6852  ->
              match uu____6852 with
              | (l,generalized_univs,t,c) ->
                  let uu____6870 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6870, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6903 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6903 with
               | None  -> None
               | Some f ->
                   let uu____6907 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____6907) in
          let is_var e1 =
            let uu____6913 =
              let uu____6914 = FStar_Syntax_Subst.compress e1 in
              uu____6914.FStar_Syntax_Syntax.n in
            match uu____6913 with
            | FStar_Syntax_Syntax.Tm_name uu____6917 -> true
            | uu____6918 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___145_6936 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_6936.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_6936.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6937 ->
                let uu___146_6938 = e2 in
                let uu____6939 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___146_6938.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6939;
                  FStar_Syntax_Syntax.pos =
                    (uu___146_6938.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___146_6938.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___147_6948 = env1 in
            let uu____6949 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___147_6948.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___147_6948.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___147_6948.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___147_6948.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___147_6948.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___147_6948.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___147_6948.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___147_6948.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___147_6948.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___147_6948.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___147_6948.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___147_6948.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___147_6948.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___147_6948.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___147_6948.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6949;
              FStar_TypeChecker_Env.is_iface =
                (uu___147_6948.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___147_6948.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___147_6948.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___147_6948.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___147_6948.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___147_6948.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___147_6948.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___147_6948.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6950 = check env2 t1 t2 in
          match uu____6950 with
          | None  ->
              let uu____6954 =
                let uu____6955 =
                  let uu____6958 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6959 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6958, uu____6959) in
                FStar_Errors.Error uu____6955 in
              raise uu____6954
          | Some g ->
              ((let uu____6964 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6964
                then
                  let uu____6965 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6965
                else ());
               (let uu____6967 = decorate e t2 in (uu____6967, g)))
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
        let uu____6991 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6991
        then
          let uu____6994 = discharge g1 in
          let uu____6995 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6994, uu____6995)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____7007 =
               let uu____7008 =
                 let uu____7009 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____7009 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____7008
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____7007
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____7011 = destruct_comp c1 in
           match uu____7011 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____7023 = FStar_TypeChecker_Env.get_range env in
                 let uu____7024 =
                   let uu____7025 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____7026 =
                     let uu____7027 = FStar_Syntax_Syntax.as_arg t in
                     let uu____7028 =
                       let uu____7030 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____7030] in
                     uu____7027 :: uu____7028 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____7025 uu____7026 in
                 uu____7024
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____7023 in
               ((let uu____7036 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____7036
                 then
                   let uu____7037 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____7037
                 else ());
                (let g2 =
                   let uu____7040 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____7040 in
                 let uu____7041 = discharge g2 in
                 let uu____7042 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____7041, uu____7042))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_7066 =
        match uu___102_7066 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____7072)::[] -> f fst1
        | uu____7085 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____7090 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____7090
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____7099 =
          let uu____7102 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____7102 in
        FStar_All.pipe_right uu____7099
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____7113 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____7113
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_7127 =
        match uu___103_7127 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____7133)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____7148)::[] ->
            let uu____7169 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____7169
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____7174 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____7181 =
          let uu____7186 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____7186) in
        let uu____7191 =
          let uu____7197 =
            let uu____7202 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____7202) in
          let uu____7207 =
            let uu____7213 =
              let uu____7218 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____7218) in
            let uu____7223 =
              let uu____7229 =
                let uu____7234 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____7234) in
              let uu____7239 =
                let uu____7245 =
                  let uu____7250 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____7250) in
                [uu____7245; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____7229 :: uu____7239 in
            uu____7213 :: uu____7223 in
          uu____7197 :: uu____7207 in
        uu____7181 :: uu____7191 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7291 =
            FStar_Util.find_map table
              (fun uu____7297  ->
                 match uu____7297 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____7310 = mk1 seen_args in Some uu____7310
                     else None) in
          (match uu____7291 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____7313 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7317 =
      let uu____7318 = FStar_Syntax_Util.un_uinst l in
      uu____7318.FStar_Syntax_Syntax.n in
    match uu____7317 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____7322 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7340)::uu____7341 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7347 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7351,Some (FStar_Syntax_Syntax.Implicit uu____7352))::uu____7353
          -> bs
      | uu____7362 ->
          let uu____7363 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7363 with
           | None  -> bs
           | Some t ->
               let uu____7366 =
                 let uu____7367 = FStar_Syntax_Subst.compress t in
                 uu____7367.FStar_Syntax_Syntax.n in
               (match uu____7366 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7371) ->
                    let uu____7382 =
                      FStar_Util.prefix_until
                        (fun uu___104_7401  ->
                           match uu___104_7401 with
                           | (uu____7405,Some (FStar_Syntax_Syntax.Implicit
                              uu____7406)) -> false
                           | uu____7408 -> true) bs' in
                    (match uu____7382 with
                     | None  -> bs
                     | Some ([],uu____7426,uu____7427) -> bs
                     | Some (imps,uu____7464,uu____7465) ->
                         let uu____7502 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7510  ->
                                   match uu____7510 with
                                   | (x,uu____7515) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7502
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7538  ->
                                     match uu____7538 with
                                     | (x,i) ->
                                         let uu____7549 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7549, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7555 -> bs))
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
              (let uu____7574 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7574 e.FStar_Syntax_Syntax.pos)
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
          let uu____7596 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7596
          then e
          else
            (let uu____7598 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7598
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
        (let uu____7624 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7624
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7626 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7626))
         else ());
        (let fv =
           let uu____7629 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7629 None in
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
         let uu____7636 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___148_7645 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___148_7645.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___148_7645.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___148_7645.FStar_Syntax_Syntax.sigmeta)
           }), uu____7636))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7655 =
        match uu___105_7655 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7656 -> false in
      let reducibility uu___106_7660 =
        match uu___106_7660 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____7661 -> false in
      let assumption uu___107_7665 =
        match uu___107_7665 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____7666 -> false in
      let reification uu___108_7670 =
        match uu___108_7670 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____7671 -> true
        | uu____7672 -> false in
      let inferred uu___109_7676 =
        match uu___109_7676 with
        | FStar_Syntax_Syntax.Discriminator uu____7677 -> true
        | FStar_Syntax_Syntax.Projector uu____7678 -> true
        | FStar_Syntax_Syntax.RecordType uu____7681 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____7686 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____7691 -> false in
      let has_eq uu___110_7695 =
        match uu___110_7695 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7696 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____7730 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7733 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7736 =
        let uu____7737 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7739  ->
                  match uu___111_7739 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7740 -> false)) in
        FStar_All.pipe_right uu____7737 Prims.op_Negation in
      if uu____7736
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7750 =
            let uu____7751 =
              let uu____7754 =
                let uu____7755 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7755 msg in
              (uu____7754, r) in
            FStar_Errors.Error uu____7751 in
          raise uu____7750 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7763 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7771 =
            let uu____7772 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7772 in
          if uu____7771 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7776),uu____7777,uu____7778) ->
              ((let uu____7789 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7789
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7792 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7792
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7796 ->
              let uu____7801 =
                let uu____7802 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7802 in
              if uu____7801 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7806 ->
              let uu____7810 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7810 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7813 ->
              let uu____7816 =
                let uu____7817 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7817 in
              if uu____7816 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7821 ->
              let uu____7822 =
                let uu____7823 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7823 in
              if uu____7822 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7827 ->
              let uu____7828 =
                let uu____7829 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7829 in
              if uu____7828 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7833 ->
              let uu____7840 =
                let uu____7841 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7841 in
              if uu____7840 then err'1 () else ()
          | uu____7845 -> ()))
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
                          let uu____7902 =
                            let uu____7905 =
                              let uu____7906 =
                                let uu____7911 =
                                  let uu____7912 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7912 in
                                (uu____7911, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7906 in
                            FStar_Syntax_Syntax.mk uu____7905 in
                          uu____7902 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7938  ->
                                  match uu____7938 with
                                  | (x,imp) ->
                                      let uu____7945 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7945, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7949 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7949 in
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
                             let uu____7958 =
                               let uu____7959 =
                                 let uu____7960 =
                                   let uu____7961 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7962 =
                                     let uu____7963 =
                                       let uu____7964 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7964 in
                                     [uu____7963] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7961
                                     uu____7962 in
                                 uu____7960 None p in
                               FStar_Syntax_Util.b2t uu____7959 in
                             FStar_Syntax_Util.refine x uu____7958 in
                           let uu____7969 =
                             let uu___149_7970 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___149_7970.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___149_7970.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7969) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7980 =
                          FStar_List.map
                            (fun uu____7990  ->
                               match uu____7990 with
                               | (x,uu____7997) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7980 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____8021  ->
                                match uu____8021 with
                                | (x,uu____8028) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____8037 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____8037)
                               ||
                               (let uu____8038 =
                                  let uu____8039 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____8039.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____8038) in
                           let quals =
                             let uu____8042 =
                               let uu____8044 =
                                 let uu____8046 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____8046
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____8049 =
                                 FStar_List.filter
                                   (fun uu___112_8051  ->
                                      match uu___112_8051 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____8052 -> false) iquals in
                               FStar_List.append uu____8044 uu____8049 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____8042 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____8065 =
                                 let uu____8066 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____8066 in
                               FStar_Syntax_Syntax.mk_Total uu____8065 in
                             let uu____8067 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____8067 in
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
                           (let uu____8070 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____8070
                            then
                              let uu____8071 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____8071
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
                                             fun uu____8099  ->
                                               match uu____8099 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____8115 =
                                                       let uu____8118 =
                                                         let uu____8119 =
                                                           let uu____8124 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____8124,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8119 in
                                                       pos uu____8118 in
                                                     (uu____8115, b)
                                                   else
                                                     (let uu____8128 =
                                                        let uu____8131 =
                                                          let uu____8132 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8132 in
                                                        pos uu____8131 in
                                                      (uu____8128, b)))) in
                                   let pat_true =
                                     let uu____8144 =
                                       let uu____8147 =
                                         let uu____8148 =
                                           let uu____8156 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____8156, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8148 in
                                       pos uu____8147 in
                                     (uu____8144, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____8178 =
                                       let uu____8181 =
                                         let uu____8182 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8182 in
                                       pos uu____8181 in
                                     (uu____8178, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____8191 =
                                     let uu____8194 =
                                       let uu____8195 =
                                         let uu____8211 =
                                           let uu____8213 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____8214 =
                                             let uu____8216 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____8216] in
                                           uu____8213 :: uu____8214 in
                                         (arg_exp, uu____8211) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8195 in
                                     FStar_Syntax_Syntax.mk uu____8194 in
                                   uu____8191 None p) in
                              let dd =
                                let uu____8227 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____8227
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
                                let uu____8239 =
                                  let uu____8242 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____8242 in
                                let uu____8243 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____8239;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____8243
                                } in
                              let impl =
                                let uu____8247 =
                                  let uu____8248 =
                                    let uu____8254 =
                                      let uu____8256 =
                                        let uu____8257 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____8257
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____8256] in
                                    ((false, [lb]), uu____8254, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____8248 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8247;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____8272 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____8272
                               then
                                 let uu____8273 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8273
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
                                fun uu____8293  ->
                                  match uu____8293 with
                                  | (a,uu____8297) ->
                                      let uu____8298 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8298 with
                                       | (field_name,uu____8302) ->
                                           let field_proj_tm =
                                             let uu____8304 =
                                               let uu____8305 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8305 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8304 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8319 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8328  ->
                                    match uu____8328 with
                                    | (x,uu____8333) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8335 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8335 with
                                         | (field_name,uu____8340) ->
                                             let t =
                                               let uu____8342 =
                                                 let uu____8343 =
                                                   let uu____8346 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8346 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8343 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8342 in
                                             let only_decl =
                                               ((let uu____8348 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____8348)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8349 =
                                                    let uu____8350 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8350.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8349) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8360 =
                                                   FStar_List.filter
                                                     (fun uu___113_8362  ->
                                                        match uu___113_8362
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8363 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8360
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_8371  ->
                                                         match uu___114_8371
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8372 ->
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
                                             ((let uu____8375 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8375
                                               then
                                                 let uu____8376 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8376
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
                                                           fun uu____8403  ->
                                                             match uu____8403
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8419
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8419,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8431
                                                                    =
                                                                    let uu____8434
                                                                    =
                                                                    let uu____8435
                                                                    =
                                                                    let uu____8440
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8440,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8435 in
                                                                    pos
                                                                    uu____8434 in
                                                                    (uu____8431,
                                                                    b))
                                                                   else
                                                                    (let uu____8444
                                                                    =
                                                                    let uu____8447
                                                                    =
                                                                    let uu____8448
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8448 in
                                                                    pos
                                                                    uu____8447 in
                                                                    (uu____8444,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8460 =
                                                     let uu____8463 =
                                                       let uu____8464 =
                                                         let uu____8472 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8472,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8464 in
                                                     pos uu____8463 in
                                                   let uu____8478 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8460, None,
                                                     uu____8478) in
                                                 let body =
                                                   let uu____8489 =
                                                     let uu____8492 =
                                                       let uu____8493 =
                                                         let uu____8509 =
                                                           let uu____8511 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8511] in
                                                         (arg_exp,
                                                           uu____8509) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8493 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8492 in
                                                   uu____8489 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8528 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8528
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
                                                   let uu____8534 =
                                                     let uu____8537 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8537 in
                                                   let uu____8538 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8534;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8538
                                                   } in
                                                 let impl =
                                                   let uu____8542 =
                                                     let uu____8543 =
                                                       let uu____8549 =
                                                         let uu____8551 =
                                                           let uu____8552 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8552
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8551] in
                                                       ((false, [lb]),
                                                         uu____8549, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8543 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8542;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8567 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8567
                                                  then
                                                    let uu____8568 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8568
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8319 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8598) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8601 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8601 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8614 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8614 with
                    | (formals,uu____8624) ->
                        let uu____8635 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8648 =
                                   let uu____8649 =
                                     let uu____8650 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8650 in
                                   FStar_Ident.lid_equals typ_lid uu____8649 in
                                 if uu____8648
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8660,uvs',tps,typ0,uu____8664,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8677 -> failwith "Impossible"
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
                        (match uu____8635 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8719 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8719 with
                              | (indices,uu____8729) ->
                                  let refine_domain =
                                    let uu____8741 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8743  ->
                                              match uu___115_8743 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8744 -> true
                                              | uu____8749 -> false)) in
                                    if uu____8741
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8756 =
                                      match uu___116_8756 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8758,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8765 -> None in
                                    let uu____8766 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8766 with
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
                                    let uu____8774 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8774 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8805  ->
                                               fun uu____8806  ->
                                                 match (uu____8805,
                                                         uu____8806)
                                                 with
                                                 | ((x,uu____8816),(x',uu____8818))
                                                     ->
                                                     let uu____8823 =
                                                       let uu____8828 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8828) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8823) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8829 -> []