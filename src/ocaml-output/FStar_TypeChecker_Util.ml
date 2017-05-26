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
              ((let uu____2202 =
                  let uu____2203 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2203 Prims.op_Negation in
                if uu____2202
                then
                  let uu____2204 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2204
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2292 = force_sort' e1 in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2292
                  | (arg::args2,(argpat,uu____2305)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2355) ->
                           let x =
                             let uu____2371 = force_sort e2 in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2371 in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2385) ->
                           let pat =
                             let uu____2400 = aux argpat e2 in
                             let uu____2401 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____2400, uu____2401) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2404 ->
                      let uu____2418 =
                        let uu____2419 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____2420 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2419 uu____2420 in
                      failwith uu____2418 in
                match_args [] args argpats))
          | uu____2427 ->
              let uu____2430 =
                let uu____2431 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____2432 = FStar_Syntax_Print.pat_to_string qq in
                let uu____2433 =
                  let uu____2434 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string) in
                  FStar_All.pipe_right uu____2434
                    (FStar_String.concat "\n\t") in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2431 uu____2432 uu____2433 in
              failwith uu____2430 in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2441) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2457,e::[]) -> aux p e
        | uu____2460 -> failwith "Unexpected number of patterns"
let rec decorated_pattern_as_term:
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list* FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty) in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p in
    let pat_as_arg uu____2497 =
      match uu____2497 with
      | (p,i) ->
          let uu____2507 = decorated_pattern_as_term p in
          (match uu____2507 with
           | (vars,te) ->
               let uu____2520 =
                 let uu____2523 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____2523) in
               (vars, uu____2520)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2530 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2538 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____2538)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2541 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____2541)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2555 =
          let uu____2563 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____2563 FStar_List.unzip in
        (match uu____2555 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____2621 =
               let uu____2622 =
                 let uu____2623 =
                   let uu____2633 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____2633, args) in
                 FStar_Syntax_Syntax.Tm_app uu____2623 in
               mk1 uu____2622 in
             (vars1, uu____2621))
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
      | (wp,uu____2662)::[] -> wp
      | uu____2675 ->
          let uu____2681 =
            let uu____2682 =
              let uu____2683 =
                FStar_List.map
                  (fun uu____2687  ->
                     match uu____2687 with
                     | (x,uu____2691) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____2683 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2682 in
          failwith uu____2681 in
    let uu____2695 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____2695, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2709 = destruct_comp c in
        match uu____2709 with
        | (u,uu____2714,wp) ->
            let uu____2716 =
              let uu____2722 =
                let uu____2723 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____2723 in
              [uu____2722] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2716;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2733 =
          let uu____2737 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____2738 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____2737 uu____2738 in
        match uu____2733 with | (m,uu____2740,uu____2741) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2751 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____2751
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
        let uu____2776 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____2776 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____2798 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____2798 with
             | (a,kwp) ->
                 let uu____2815 = destruct_comp m1 in
                 let uu____2819 = destruct_comp m2 in
                 ((md, a, kwp), uu____2815, uu____2819))
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
            let uu____2867 =
              let uu____2868 =
                let uu____2874 = FStar_Syntax_Syntax.as_arg wp in
                [uu____2874] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2868;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____2867
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
      let uu___129_2910 = lc in
      let uu____2911 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___129_2910.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____2911;
        FStar_Syntax_Syntax.cflags =
          (uu___129_2910.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____2914  ->
             let uu____2915 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____2915)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2919 =
      let uu____2920 = FStar_Syntax_Subst.compress t in
      uu____2920.FStar_Syntax_Syntax.n in
    match uu____2919 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2923 -> true
    | uu____2931 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2943 = FStar_Syntax_Util.is_ml_comp c in
        if uu____2943
        then c
        else
          (let uu____2945 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____2945
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2975 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____2975] in
                       let us =
                         let uu____2978 =
                           let uu____2980 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____2980] in
                         u_res :: uu____2978 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (Some
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))) in
                       let uu____2991 =
                         let uu____2992 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____2993 =
                           let uu____2994 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____2995 =
                             let uu____2997 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____2998 =
                               let uu____3000 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____3000] in
                             uu____2997 :: uu____2998 in
                           uu____2994 :: uu____2995 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2992 uu____2993 in
                       uu____2991 None wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____3006 = destruct_comp c1 in
              match uu____3006 with
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
        let close1 uu____3029 =
          let uu____3030 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____3030 in
        let uu___130_3031 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___130_3031.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___130_3031.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___130_3031.FStar_Syntax_Syntax.cflags);
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
          let uu____3042 =
            let uu____3043 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____3043 in
          if uu____3042
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Syntax_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____3048 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____3048
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____3050 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid in
                  match uu____3050 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____3056 =
                        let uu____3057 =
                          let uu____3058 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____3059 =
                            let uu____3060 = FStar_Syntax_Syntax.as_arg t in
                            let uu____3061 =
                              let uu____3063 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____3063] in
                            uu____3060 :: uu____3061 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3058 uu____3059 in
                        uu____3057 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____3056) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____3069 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____3069
         then
           let uu____3070 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____3071 = FStar_Syntax_Print.term_to_string v1 in
           let uu____3072 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____3070
             uu____3071 uu____3072
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
          fun uu____3089  ->
            match uu____3089 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____3099 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____3099
                  then
                    let bstr =
                      match b with
                      | None  -> "none"
                      | Some x -> FStar_Syntax_Print.bv_to_string x in
                    let uu____3102 =
                      match e1opt with
                      | None  -> "None"
                      | Some e -> FStar_Syntax_Print.term_to_string e in
                    let uu____3104 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____3105 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____3102 uu____3104 bstr uu____3105
                  else ());
                 (let bind_it uu____3110 =
                    let uu____3111 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____3111
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____3121 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____3121
                        then
                          let uu____3122 =
                            match b with
                            | None  -> "none"
                            | Some x -> FStar_Syntax_Print.bv_to_string x in
                          let uu____3124 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____3125 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____3126 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____3127 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____3122 uu____3124 uu____3125 uu____3126
                            uu____3127
                        else ());
                       (let try_simplify uu____3138 =
                          let aux uu____3148 =
                            let uu____3149 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____3149
                            then
                              match b with
                              | None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | Some uu____3168 ->
                                  let uu____3169 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____3169
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____3188 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____3188
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (Some e,Some x) ->
                                let uu____3224 =
                                  let uu____3227 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____3227, reason) in
                                FStar_Util.Inl uu____3224
                            | uu____3230 -> aux () in
                          let rec maybe_close t x c =
                            let uu____3245 =
                              let uu____3246 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____3246.FStar_Syntax_Syntax.n in
                            match uu____3245 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____3250) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Syntax_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____3256 -> c in
                          let uu____3257 =
                            let uu____3258 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Syntax_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____3258 in
                          if uu____3257
                          then
                            let uu____3266 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____3266
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____3280 =
                                  let uu____3281 =
                                    let uu____3284 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____3284) in
                                  FStar_Errors.Error uu____3281 in
                                raise uu____3280))
                          else
                            (let uu____3292 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____3292
                             then subst_c2 "both total"
                             else
                               (let uu____3300 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____3300
                                then
                                  let uu____3307 =
                                    let uu____3310 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____3310, "both gtot") in
                                  FStar_Util.Inl uu____3307
                                else
                                  (match (e1opt, b) with
                                   | (Some e,Some x) ->
                                       let uu____3326 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____3327 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____3327) in
                                       if uu____3326
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___131_3336 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___131_3336.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___131_3336.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____3337 =
                                           let uu____3340 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____3340, "c1 Tot") in
                                         FStar_Util.Inl uu____3337
                                       else aux ()
                                   | uu____3344 -> aux ()))) in
                        let uu____3349 = try_simplify () in
                        match uu____3349 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____3367 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____3367
                              then
                                let uu____3368 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____3369 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____3370 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____3368 uu____3369 uu____3370
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____3377 = lift_and_destruct env c1 c2 in
                            (match uu____3377 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | None  ->
                                       let uu____3411 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____3411]
                                   | Some x ->
                                       let uu____3413 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____3413] in
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
                                   let uu____3436 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____3437 =
                                     let uu____3439 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____3440 =
                                       let uu____3442 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____3443 =
                                         let uu____3445 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____3446 =
                                           let uu____3448 =
                                             let uu____3449 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____3449 in
                                           [uu____3448] in
                                         uu____3445 :: uu____3446 in
                                       uu____3442 :: uu____3443 in
                                     uu____3439 :: uu____3440 in
                                   uu____3436 :: uu____3437 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____3454 =
                                     let uu____3455 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____3455
                                       wp_args in
                                   uu____3454 None t2.FStar_Syntax_Syntax.pos in
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
              let uu____3499 =
                let uu____3500 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____3500 in
              if uu____3499
              then f
              else (let uu____3502 = reason1 () in label uu____3502 r f)
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
            let uu___132_3513 = g in
            let uu____3514 =
              let uu____3515 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____3515 in
            {
              FStar_TypeChecker_Env.guard_f = uu____3514;
              FStar_TypeChecker_Env.deferred =
                (uu___132_3513.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_3513.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_3513.FStar_TypeChecker_Env.implicits)
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
      | uu____3527 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3544 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____3548 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3548
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____3555 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____3555
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____3560 = destruct_comp c1 in
                    match uu____3560 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____3573 =
                            let uu____3574 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____3575 =
                              let uu____3576 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____3577 =
                                let uu____3579 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____3580 =
                                  let uu____3582 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____3582] in
                                uu____3579 :: uu____3580 in
                              uu____3576 :: uu____3577 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3574
                              uu____3575 in
                          uu____3573 None wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___133_3587 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___133_3587.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___133_3587.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___133_3587.FStar_Syntax_Syntax.cflags);
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
            let uu____3614 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____3614
            then (lc, g0)
            else
              ((let uu____3619 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____3619
                then
                  let uu____3620 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____3621 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3620 uu____3621
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___98_3627  ->
                          match uu___98_3627 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3629 -> [])) in
                let strengthen uu____3635 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____3643 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____3643 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____3650 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____3651 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____3651) in
                           if uu____3650
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 None (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____3658 =
                                 let uu____3659 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____3659 in
                               FStar_Syntax_Util.comp_set_flags uu____3658
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env (Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____3664 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____3664
                           then
                             let uu____3665 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____3666 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____3665 uu____3666
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____3669 = destruct_comp c2 in
                           match uu____3669 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____3682 =
                                   let uu____3683 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____3684 =
                                     let uu____3685 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____3686 =
                                       let uu____3688 =
                                         let uu____3689 =
                                           let uu____3690 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____3690 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3689 in
                                       let uu____3691 =
                                         let uu____3693 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____3693] in
                                       uu____3688 :: uu____3691 in
                                     uu____3685 :: uu____3686 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____3683
                                     uu____3684 in
                                 uu____3682 None wp.FStar_Syntax_Syntax.pos in
                               ((let uu____3699 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____3699
                                 then
                                   let uu____3700 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____3700
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____3703 =
                  let uu___134_3704 = lc in
                  let uu____3705 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____3706 =
                    let uu____3708 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3709 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____3709) in
                    if uu____3708 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____3705;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___134_3704.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____3706;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____3703,
                  (let uu___135_3712 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___135_3712.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___135_3712.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___135_3712.FStar_TypeChecker_Env.implicits)
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
        let uu____3727 =
          let uu____3730 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____3731 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____3730, uu____3731) in
        match uu____3727 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____3740 =
                let uu____3741 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____3742 =
                  let uu____3743 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3744 =
                    let uu____3746 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____3746] in
                  uu____3743 :: uu____3744 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3741 uu____3742 in
              uu____3740 None res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____3754 =
                let uu____3755 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____3756 =
                  let uu____3757 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3758 =
                    let uu____3760 =
                      let uu____3761 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3761 in
                    let uu____3762 =
                      let uu____3764 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____3764] in
                    uu____3760 :: uu____3762 in
                  uu____3757 :: uu____3758 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3755 uu____3756 in
              uu____3754 None res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____3772 =
                let uu____3773 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____3774 =
                  let uu____3775 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____3776 =
                    let uu____3778 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____3779 =
                      let uu____3781 =
                        let uu____3782 =
                          let uu____3783 =
                            let uu____3784 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____3784] in
                          FStar_Syntax_Util.abs uu____3783 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL]))) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3782 in
                      [uu____3781] in
                    uu____3778 :: uu____3779 in
                  uu____3775 :: uu____3776 in
                FStar_Syntax_Syntax.mk_Tm_app uu____3773 uu____3774 in
              uu____3772 None res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____3800 = FStar_TypeChecker_Env.get_range env in
              bind uu____3800 env None (FStar_Syntax_Util.lcomp_of_comp comp)
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
          let comp uu____3818 =
            let uu____3819 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____3819
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____3822 =
                 let uu____3835 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____3836 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____3835 uu____3836 in
               match uu____3822 with
               | ((md,uu____3838,uu____3839),(u_res_t,res_t,wp_then),
                  (uu____3843,uu____3844,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____3873 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____3874 =
                       let uu____3875 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____3876 =
                         let uu____3877 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____3878 =
                           let uu____3880 = FStar_Syntax_Syntax.as_arg g in
                           let uu____3881 =
                             let uu____3883 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____3884 =
                               let uu____3886 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____3886] in
                             uu____3883 :: uu____3884 in
                           uu____3880 :: uu____3881 in
                         uu____3877 :: uu____3878 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3875 uu____3876 in
                     uu____3874 None uu____3873 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____3894 =
                     let uu____3895 = FStar_Options.split_cases () in
                     uu____3895 > (Prims.parse_int "0") in
                   if uu____3894
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____3901 =
                          let uu____3902 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____3903 =
                            let uu____3904 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____3905 =
                              let uu____3907 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____3907] in
                            uu____3904 :: uu____3905 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____3902 uu____3903 in
                        uu____3901 None wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____3912 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____3912;
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
      let uu____3919 =
        let uu____3920 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____3920 in
      FStar_Syntax_Syntax.fvar uu____3919 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____3940  ->
                 match uu____3940 with
                 | (uu____3943,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Syntax_Const.effect_PURE_lid lcases in
        let bind_cases uu____3948 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____3950 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____3950
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____3970 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____3971 =
                 let uu____3972 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____3973 =
                   let uu____3974 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____3975 =
                     let uu____3977 = FStar_Syntax_Syntax.as_arg g in
                     let uu____3978 =
                       let uu____3980 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____3981 =
                         let uu____3983 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____3983] in
                       uu____3980 :: uu____3981 in
                     uu____3977 :: uu____3978 in
                   uu____3974 :: uu____3975 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____3972 uu____3973 in
               uu____3971 None uu____3970 in
             let default_case =
               let post_k =
                 let uu____3992 =
                   let uu____3996 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____3996] in
                 let uu____3997 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____3992 uu____3997 in
               let kwp =
                 let uu____4003 =
                   let uu____4007 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____4007] in
                 let uu____4008 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____4003 uu____4008 in
               let post = FStar_Syntax_Syntax.new_bv None post_k in
               let wp =
                 let uu____4013 =
                   let uu____4014 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____4014] in
                 let uu____4015 =
                   let uu____4016 =
                     let uu____4019 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____4019 in
                   let uu____4020 =
                     fvar_const env FStar_Syntax_Const.false_lid in
                   FStar_All.pipe_left uu____4016 uu____4020 in
                 FStar_Syntax_Util.abs uu____4013 uu____4015
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
                 (fun uu____4034  ->
                    fun celse  ->
                      match uu____4034 with
                      | (g,cthen) ->
                          let uu____4040 =
                            let uu____4053 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____4053 celse in
                          (match uu____4040 with
                           | ((md,uu____4055,uu____4056),(uu____4057,uu____4058,wp_then),
                              (uu____4060,uu____4061,wp_else)) ->
                               let uu____4072 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____4072 []))
                 lcases default_case in
             let uu____4073 =
               let uu____4074 = FStar_Options.split_cases () in
               uu____4074 > (Prims.parse_int "0") in
             if uu____4073
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____4078 = destruct_comp comp1 in
                match uu____4078 with
                | (uu____4082,uu____4083,wp) ->
                    let wp1 =
                      let uu____4088 =
                        let uu____4089 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____4090 =
                          let uu____4091 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____4092 =
                            let uu____4094 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____4094] in
                          uu____4091 :: uu____4092 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4089 uu____4090 in
                      uu____4088 None wp.FStar_Syntax_Syntax.pos in
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
          let uu____4110 =
            ((let uu____4111 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____4111) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____4112 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____4112) in
          if uu____4110
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____4120 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4124 =
            (let uu____4125 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____4125) || env.FStar_TypeChecker_Env.lax in
          if uu____4124
          then c
          else
            (let uu____4129 = FStar_Syntax_Util.is_partial_return c in
             if uu____4129
             then c
             else
               (let uu____4133 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____4133
                then
                  let uu____4136 =
                    let uu____4137 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Syntax_Const.effect_GTot_lid in
                    Prims.op_Negation uu____4137 in
                  (if uu____4136
                   then
                     let uu____4140 =
                       let uu____4141 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____4142 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____4141 uu____4142 in
                     failwith uu____4140
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____4147 =
                        let uu____4148 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____4148 in
                      if uu____4147
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___136_4153 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___136_4153.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Syntax_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___136_4153.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___136_4153.FStar_Syntax_Syntax.effect_args);
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
                     let uu____4164 =
                       let uu____4167 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____4167
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____4164 in
                   let eq1 =
                     let uu____4171 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____4171 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____4173 =
                     let uu____4174 =
                       let uu____4179 =
                         bind e.FStar_Syntax_Syntax.pos env None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((Some x), eq_ret) in
                       uu____4179.FStar_Syntax_Syntax.comp in
                     uu____4174 () in
                   FStar_Syntax_Util.comp_set_flags uu____4173 flags))) in
        let uu___137_4181 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___137_4181.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___137_4181.FStar_Syntax_Syntax.res_typ);
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
          let uu____4200 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____4200 with
          | None  ->
              let uu____4205 =
                let uu____4206 =
                  let uu____4209 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____4210 = FStar_TypeChecker_Env.get_range env in
                  (uu____4209, uu____4210) in
                FStar_Errors.Error uu____4206 in
              raise uu____4205
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
            let uu____4236 =
              let uu____4237 = FStar_Syntax_Subst.compress t2 in
              uu____4237.FStar_Syntax_Syntax.n in
            match uu____4236 with
            | FStar_Syntax_Syntax.Tm_type uu____4240 -> true
            | uu____4241 -> false in
          let uu____4242 =
            let uu____4243 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____4243.FStar_Syntax_Syntax.n in
          match uu____4242 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____4249 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Syntax_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) None in
              let lc1 =
                let uu____4256 =
                  let uu____4257 =
                    let uu____4258 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____4258 in
                  (None, uu____4257) in
                bind e.FStar_Syntax_Syntax.pos env (Some e) lc uu____4256 in
              let e1 =
                let uu____4267 =
                  let uu____4268 =
                    let uu____4269 = FStar_Syntax_Syntax.as_arg e in
                    [uu____4269] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4268 in
                uu____4267
                  (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____4276 -> (e, lc)
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
              (let uu____4296 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____4296 with
               | Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____4309 -> false) in
          let gopt =
            if use_eq
            then
              let uu____4321 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____4321, false)
            else
              (let uu____4325 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____4325, true)) in
          match gopt with
          | (None ,uu____4331) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.res_typ t;
               (e,
                 ((let uu___138_4334 = lc in
                   {
                     FStar_Syntax_Syntax.eff_name =
                       (uu___138_4334.FStar_Syntax_Syntax.eff_name);
                     FStar_Syntax_Syntax.res_typ = t;
                     FStar_Syntax_Syntax.cflags =
                       (uu___138_4334.FStar_Syntax_Syntax.cflags);
                     FStar_Syntax_Syntax.comp =
                       (uu___138_4334.FStar_Syntax_Syntax.comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4338 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____4338 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___139_4343 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_4343.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_4343.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___139_4343.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___140_4346 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___140_4346.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___140_4346.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___140_4346.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____4352 =
                     let uu____4353 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____4353
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f in
                        let uu____4358 =
                          let uu____4359 = FStar_Syntax_Subst.compress f1 in
                          uu____4359.FStar_Syntax_Syntax.n in
                        match uu____4358 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4364,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4366;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4367;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4368;_},uu____4369)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___141_4393 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___141_4393.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___141_4393.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___141_4393.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____4394 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____4399 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____4399
                              then
                                let uu____4400 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____4401 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____4402 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____4403 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4400 uu____4401 uu____4402 uu____4403
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____4406 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Syntax_Const.effect_PURE_lid in
                              match uu____4406 with
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
                                  let uu____4417 = destruct_comp ct in
                                  (match uu____4417 with
                                   | (u_t,uu____4424,uu____4425) ->
                                       let wp =
                                         let uu____4429 =
                                           let uu____4430 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____4431 =
                                             let uu____4432 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____4433 =
                                               let uu____4435 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4435] in
                                             uu____4432 :: uu____4433 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4430 uu____4431 in
                                         uu____4429
                                           (Some (k.FStar_Syntax_Syntax.n))
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____4441 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____4441 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____4451 =
                                             let uu____4452 =
                                               let uu____4453 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____4453] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____4452 in
                                           uu____4451
                                             (Some
                                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____4459 =
                                         let uu____4462 =
                                           FStar_All.pipe_left
                                             (fun _0_29  -> Some _0_29)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____4473 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____4474 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____4462
                                           uu____4473 e cret uu____4474 in
                                       (match uu____4459 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___142_4480 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___142_4480.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___142_4480.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____4482 =
                                                let uu____4483 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____4483 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env (Some e) uu____4482
                                                ((Some x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____4493 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____4493
                                              then
                                                let uu____4494 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____4494
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___99_4500  ->
                             match uu___99_4500 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4502 -> [])) in
                   let lc1 =
                     let uu___143_4504 = lc in
                     let uu____4505 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____4505;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___144_4507 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_4507.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_4507.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_4507.FStar_TypeChecker_Env.implicits)
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
        let uu____4527 =
          let uu____4528 =
            let uu____4529 =
              let uu____4530 =
                let uu____4531 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____4531 in
              [uu____4530] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4529 in
          uu____4528 None res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____4527 in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____4540 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____4540
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
                | (req,uu____4564)::(ens,uu____4566)::uu____4567 ->
                    let uu____4589 =
                      let uu____4591 = norm req in Some uu____4591 in
                    let uu____4592 =
                      let uu____4593 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm uu____4593 in
                    (uu____4589, uu____4592)
                | uu____4595 ->
                    let uu____4601 =
                      let uu____4602 =
                        let uu____4605 =
                          let uu____4606 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4606 in
                        (uu____4605, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____4602 in
                    raise uu____4601)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4616)::uu____4617 ->
                    let uu____4631 =
                      let uu____4634 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Syntax_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives.fst uu____4634 in
                    (match uu____4631 with
                     | (us_r,uu____4651) ->
                         let uu____4652 =
                           let uu____4655 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Syntax_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives.fst
                             uu____4655 in
                         (match uu____4652 with
                          | (us_e,uu____4672) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____4675 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4675
                                  us_r in
                              let as_ens =
                                let uu____4677 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Syntax_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____4677
                                  us_e in
                              let req =
                                let uu____4681 =
                                  let uu____4682 =
                                    let uu____4683 =
                                      let uu____4690 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4690] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4683 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____4682 in
                                uu____4681
                                  (Some
                                     (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____4706 =
                                  let uu____4707 =
                                    let uu____4708 =
                                      let uu____4715 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____4715] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (Some FStar_Syntax_Syntax.imp_tag)) ::
                                      uu____4708 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____4707 in
                                uu____4706 None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____4728 =
                                let uu____4730 = norm req in Some uu____4730 in
                              let uu____4731 =
                                let uu____4732 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm uu____4732 in
                              (uu____4728, uu____4731)))
                | uu____4734 -> failwith "Impossible"))
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
      (let uu____4754 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____4754
       then
         let uu____4755 = FStar_Syntax_Print.term_to_string tm in
         let uu____4756 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____4755 uu____4756
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
        (let uu____4777 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____4777
         then
           let uu____4778 = FStar_Syntax_Print.term_to_string tm in
           let uu____4779 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____4778
             uu____4779
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____4784 =
      let uu____4785 =
        let uu____4786 = FStar_Syntax_Subst.compress t in
        uu____4786.FStar_Syntax_Syntax.n in
      match uu____4785 with
      | FStar_Syntax_Syntax.Tm_app uu____4789 -> false
      | uu____4799 -> true in
    if uu____4784
    then t
    else
      (let uu____4801 = FStar_Syntax_Util.head_and_args t in
       match uu____4801 with
       | (head1,args) ->
           let uu____4827 =
             let uu____4828 =
               let uu____4829 = FStar_Syntax_Subst.compress head1 in
               uu____4829.FStar_Syntax_Syntax.n in
             match uu____4828 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____4832 -> false in
           if uu____4827
           then
             (match args with
              | x::[] -> fst x
              | uu____4848 ->
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
             let uu____4876 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____4876 with
             | (formals,uu____4885) ->
                 let n_implicits =
                   let uu____4897 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4934  ->
                             match uu____4934 with
                             | (uu____4938,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality)))) in
                   match uu____4897 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____5010 = FStar_TypeChecker_Env.expected_typ env in
             match uu____5010 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____5024 =
                     let uu____5025 =
                       let uu____5028 =
                         let uu____5029 = FStar_Util.string_of_int n_expected in
                         let uu____5033 = FStar_Syntax_Print.term_to_string e in
                         let uu____5034 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____5029 uu____5033 uu____5034 in
                       let uu____5038 = FStar_TypeChecker_Env.get_range env in
                       (uu____5028, uu____5038) in
                     FStar_Errors.Error uu____5025 in
                   raise uu____5024
                 else Some (n_available - n_expected) in
           let decr_inst uu___100_5051 =
             match uu___100_5051 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____5070 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____5070 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_30,uu____5131) when
                          _0_30 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____5153,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____5172 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____5172 with
                           | (v1,uu____5193,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____5203 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____5203 with
                                | (args,bs3,subst3,g') ->
                                    let uu____5252 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____5252)))
                      | (uu____5266,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____5290 =
                      let uu____5304 = inst_n_binders t in
                      aux [] uu____5304 bs1 in
                    (match uu____5290 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____5342) -> (e, torig, guard)
                          | (uu____5358,[]) when
                              let uu____5374 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____5374 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____5375 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____5394 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____5409 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs univs1 =
  let uu____5421 =
    let uu____5423 = FStar_Util.set_elements univs1 in
    FStar_All.pipe_right uu____5423
      (FStar_List.map
         (fun u  ->
            let uu____5433 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____5433 FStar_Util.string_of_int)) in
  FStar_All.pipe_right uu____5421 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5445 = FStar_Util.set_is_empty x in
      if uu____5445
      then []
      else
        (let s =
           let uu____5450 =
             let uu____5452 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____5452 in
           FStar_All.pipe_right uu____5450 FStar_Util.set_elements in
         (let uu____5457 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____5457
          then
            let uu____5458 =
              let uu____5459 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____5459 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5458
          else ());
         (let r =
            let uu____5467 = FStar_TypeChecker_Env.get_range env in
            Some uu____5467 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____5479 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____5479
                     then
                       let uu____5480 =
                         let uu____5481 = FStar_Unionfind.uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5481 in
                       let uu____5483 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____5484 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5480 uu____5483 uu____5484
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
        let uu____5502 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____5502 FStar_Util.fifo_set_elements in
      univnames1
let maybe_set_tk ts uu___101_5529 =
  match uu___101_5529 with
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
        | ([],uu____5570) -> generalized_univ_names
        | (uu____5574,[]) -> explicit_univ_names
        | uu____5578 ->
            let uu____5583 =
              let uu____5584 =
                let uu____5587 =
                  let uu____5588 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5588 in
                (uu____5587, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____5584 in
            raise uu____5583
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
      (let uu____5602 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____5602
       then
         let uu____5603 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____5603
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____5609 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____5609
        then
          let uu____5610 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____5610
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t in
        let uu____5615 = FStar_ST.read t0.FStar_Syntax_Syntax.tk in
        maybe_set_tk (univs2, ts) uu____5615))
let gen:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.comp) Prims.list option
  =
  fun env  ->
    fun ecs  ->
      let uu____5645 =
        let uu____5646 =
          FStar_Util.for_all
            (fun uu____5651  ->
               match uu____5651 with
               | (uu____5656,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs in
        FStar_All.pipe_left Prims.op_Negation uu____5646 in
      if uu____5645
      then None
      else
        (let norm c =
           (let uu____5679 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium in
            if uu____5679
            then
              let uu____5680 = FStar_Syntax_Print.comp_to_string c in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5680
            else ());
           (let c1 =
              let uu____5683 = FStar_TypeChecker_Env.should_verify env in
              if uu____5683
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c in
            (let uu____5686 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium in
             if uu____5686
             then
               let uu____5687 = FStar_Syntax_Print.comp_to_string c1 in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5687
             else ());
            c1) in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
         let gen_uvars uvs =
           let uu____5721 = FStar_Util.set_difference uvs env_uvars in
           FStar_All.pipe_right uu____5721 FStar_Util.set_elements in
         let uu____5765 =
           let uu____5783 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5838  ->
                     match uu____5838 with
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
           FStar_All.pipe_right uu____5783 FStar_List.unzip in
         match uu____5765 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1 in
             let gen_univs1 = gen_univs env univs2 in
             ((let uu____6000 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____6000
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
                      (fun uu____6042  ->
                         match uu____6042 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____6099  ->
                                       match uu____6099 with
                                       | (u,k) ->
                                           let uu____6119 =
                                             FStar_Unionfind.find u in
                                           (match uu____6119 with
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
                                                uu____6157 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____6165 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k in
                                                let uu____6170 =
                                                  FStar_Syntax_Util.arrow_formals
                                                    k1 in
                                                (match uu____6170 with
                                                 | (bs,kres) ->
                                                     let a =
                                                       let uu____6194 =
                                                         let uu____6196 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env in
                                                         FStar_All.pipe_left
                                                           (fun _0_31  ->
                                                              Some _0_31)
                                                           uu____6196 in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____6194 kres in
                                                     let t =
                                                       let uu____6199 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a in
                                                       let uu____6200 =
                                                         let uu____6207 =
                                                           let uu____6213 =
                                                             let uu____6214 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres in
                                                             FStar_Syntax_Util.lcomp_of_comp
                                                               uu____6214 in
                                                           FStar_Util.Inl
                                                             uu____6213 in
                                                         Some uu____6207 in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____6199
                                                         uu____6200 in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag))))))) in
                             let uu____6229 =
                               match (tvars, gen_univs1) with
                               | ([],[]) ->
                                   let uu____6247 =
                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                       env e in
                                   (uu____6247, c)
                               | ([],uu____6248) ->
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
                               | uu____6260 ->
                                   let uu____6268 = (e, c) in
                                   (match uu____6268 with
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
                                          let uu____6280 =
                                            let uu____6281 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____6281.FStar_Syntax_Syntax.n in
                                          match uu____6280 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____6298 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____6298 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____6308 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs tvars e1
                                            (Some
                                               (FStar_Util.Inl
                                                  (FStar_Syntax_Util.lcomp_of_comp
                                                     c1))) in
                                        let uu____6318 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____6318)) in
                             (match uu____6229 with
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
      (let uu____6356 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
       if uu____6356
       then
         let uu____6357 =
           let uu____6358 =
             FStar_List.map
               (fun uu____6363  ->
                  match uu____6363 with
                  | (lb,uu____6368,uu____6369) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs in
           FStar_All.pipe_right uu____6358 (FStar_String.concat ", ") in
         FStar_Util.print1 "Generalizing: %s\n" uu____6357
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____6379  ->
              match uu____6379 with | (l,t,c) -> gather_free_univnames env t)
           lecs in
       let generalized_lecs =
         let uu____6394 =
           let uu____6401 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6417  ->
                     match uu____6417 with | (uu____6423,e,c) -> (e, c))) in
           gen env uu____6401 in
         match uu____6394 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____6455  ->
                     match uu____6455 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6499  ->
                  fun uu____6500  ->
                    match (uu____6499, uu____6500) with
                    | ((l,uu____6533,uu____6534),(us,e,c)) ->
                        ((let uu____6560 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium in
                          if uu____6560
                          then
                            let uu____6561 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos in
                            let uu____6562 =
                              FStar_Syntax_Print.lbname_to_string l in
                            let uu____6563 =
                              FStar_Syntax_Print.term_to_string
                                (FStar_Syntax_Util.comp_result c) in
                            let uu____6564 =
                              FStar_Syntax_Print.term_to_string e in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6561 uu____6562 uu____6563 uu____6564
                          else ());
                         (l, us, e, c))) lecs ecs in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6583  ->
              match uu____6583 with
              | (l,generalized_univs,t,c) ->
                  let uu____6601 =
                    check_universe_generalization univnames1
                      generalized_univs t in
                  (l, uu____6601, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____6634 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____6634 with
               | None  -> None
               | Some f ->
                   let uu____6638 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left (fun _0_32  -> Some _0_32) uu____6638) in
          let is_var e1 =
            let uu____6644 =
              let uu____6645 = FStar_Syntax_Subst.compress e1 in
              uu____6645.FStar_Syntax_Syntax.n in
            match uu____6644 with
            | FStar_Syntax_Syntax.Tm_name uu____6648 -> true
            | uu____6649 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___145_6667 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_6667.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_6667.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6668 ->
                let uu___146_6669 = e2 in
                let uu____6670 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)) in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___146_6669.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6670;
                  FStar_Syntax_Syntax.pos =
                    (uu___146_6669.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___146_6669.FStar_Syntax_Syntax.vars)
                } in
          let env2 =
            let uu___147_6679 = env1 in
            let uu____6680 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___147_6679.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___147_6679.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___147_6679.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___147_6679.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___147_6679.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___147_6679.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___147_6679.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___147_6679.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___147_6679.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___147_6679.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___147_6679.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___147_6679.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___147_6679.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___147_6679.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___147_6679.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6680;
              FStar_TypeChecker_Env.is_iface =
                (uu___147_6679.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___147_6679.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___147_6679.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___147_6679.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___147_6679.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___147_6679.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___147_6679.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___147_6679.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____6681 = check env2 t1 t2 in
          match uu____6681 with
          | None  ->
              let uu____6685 =
                let uu____6686 =
                  let uu____6689 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____6690 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____6689, uu____6690) in
                FStar_Errors.Error uu____6686 in
              raise uu____6685
          | Some g ->
              ((let uu____6695 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____6695
                then
                  let uu____6696 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6696
                else ());
               (let uu____6698 = decorate e t2 in (uu____6698, g)))
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
        let uu____6722 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____6722
        then
          let uu____6725 = discharge g1 in
          let uu____6726 = lc.FStar_Syntax_Syntax.comp () in
          (uu____6725, uu____6726)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____6738 =
               let uu____6739 =
                 let uu____6740 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____6740 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____6739
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____6738
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____6742 = destruct_comp c1 in
           match uu____6742 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____6754 = FStar_TypeChecker_Env.get_range env in
                 let uu____6755 =
                   let uu____6756 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____6757 =
                     let uu____6758 = FStar_Syntax_Syntax.as_arg t in
                     let uu____6759 =
                       let uu____6761 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____6761] in
                     uu____6758 :: uu____6759 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6756 uu____6757 in
                 uu____6755
                   (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                   uu____6754 in
               ((let uu____6767 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____6767
                 then
                   let uu____6768 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____6768
                 else ());
                (let g2 =
                   let uu____6771 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____6771 in
                 let uu____6772 = discharge g2 in
                 let uu____6773 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____6772, uu____6773))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___102_6797 =
        match uu___102_6797 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6803)::[] -> f fst1
        | uu____6816 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____6821 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____6821
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33) in
      let op_or_e e =
        let uu____6830 =
          let uu____6833 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____6833 in
        FStar_All.pipe_right uu____6830
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35) in
      let op_or_t t =
        let uu____6844 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____6844
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37) in
      let short_op_ite uu___103_6858 =
        match uu___103_6858 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6864)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6879)::[] ->
            let uu____6900 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____6900
              (fun _0_38  -> FStar_TypeChecker_Common.NonTrivial _0_38)
        | uu____6905 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____6912 =
          let uu____6917 = short_bin_op op_and_e in
          (FStar_Syntax_Const.op_And, uu____6917) in
        let uu____6922 =
          let uu____6928 =
            let uu____6933 = short_bin_op op_or_e in
            (FStar_Syntax_Const.op_Or, uu____6933) in
          let uu____6938 =
            let uu____6944 =
              let uu____6949 = short_bin_op op_and_t in
              (FStar_Syntax_Const.and_lid, uu____6949) in
            let uu____6954 =
              let uu____6960 =
                let uu____6965 = short_bin_op op_or_t in
                (FStar_Syntax_Const.or_lid, uu____6965) in
              let uu____6970 =
                let uu____6976 =
                  let uu____6981 = short_bin_op op_imp_t in
                  (FStar_Syntax_Const.imp_lid, uu____6981) in
                [uu____6976; (FStar_Syntax_Const.ite_lid, short_op_ite)] in
              uu____6960 :: uu____6970 in
            uu____6944 :: uu____6954 in
          uu____6928 :: uu____6938 in
        uu____6912 :: uu____6922 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7022 =
            FStar_Util.find_map table
              (fun uu____7028  ->
                 match uu____7028 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____7041 = mk1 seen_args in Some uu____7041
                     else None) in
          (match uu____7022 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____7044 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____7048 =
      let uu____7049 = FStar_Syntax_Util.un_uinst l in
      uu____7049.FStar_Syntax_Syntax.n in
    match uu____7048 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____7053 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____7071)::uu____7072 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____7078 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____7082,Some (FStar_Syntax_Syntax.Implicit uu____7083))::uu____7084
          -> bs
      | uu____7093 ->
          let uu____7094 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____7094 with
           | None  -> bs
           | Some t ->
               let uu____7097 =
                 let uu____7098 = FStar_Syntax_Subst.compress t in
                 uu____7098.FStar_Syntax_Syntax.n in
               (match uu____7097 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____7102) ->
                    let uu____7113 =
                      FStar_Util.prefix_until
                        (fun uu___104_7132  ->
                           match uu___104_7132 with
                           | (uu____7136,Some (FStar_Syntax_Syntax.Implicit
                              uu____7137)) -> false
                           | uu____7139 -> true) bs' in
                    (match uu____7113 with
                     | None  -> bs
                     | Some ([],uu____7157,uu____7158) -> bs
                     | Some (imps,uu____7195,uu____7196) ->
                         let uu____7233 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____7241  ->
                                   match uu____7241 with
                                   | (x,uu____7246) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____7233
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____7269  ->
                                     match uu____7269 with
                                     | (x,i) ->
                                         let uu____7280 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____7280, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____7286 -> bs))
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
              (let uu____7305 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_meta
                    (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                 uu____7305 e.FStar_Syntax_Syntax.pos)
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
          let uu____7327 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid) in
          if uu____7327
          then e
          else
            (let uu____7329 = FStar_ST.read e.FStar_Syntax_Syntax.tk in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_meta
                  (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))) uu____7329
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
        (let uu____7355 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____7355
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____7357 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____7357))
         else ());
        (let fv =
           let uu____7360 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____7360 None in
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
         let uu____7367 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv) None
             FStar_Range.dummyRange in
         ((let uu___148_7376 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___148_7376.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___148_7376.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___148_7376.FStar_Syntax_Syntax.sigmeta)
           }), uu____7367))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___105_7386 =
        match uu___105_7386 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7387 -> false in
      let reducibility uu___106_7391 =
        match uu___106_7391 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7392 -> false in
      let assumption uu___107_7396 =
        match uu___107_7396 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7397 -> false in
      let reification uu___108_7401 =
        match uu___108_7401 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7403 -> false in
      let inferred uu___109_7407 =
        match uu___109_7407 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7412 -> false in
      let has_eq uu___110_7416 =
        match uu___110_7416 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7417 -> false in
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
        | uu____7442 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____7445 =
        let uu____7446 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___111_7448  ->
                  match uu___111_7448 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7449 -> false)) in
        FStar_All.pipe_right uu____7446 Prims.op_Negation in
      if uu____7445
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____7459 =
            let uu____7460 =
              let uu____7463 =
                let uu____7464 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7464 msg in
              (uu____7463, r) in
            FStar_Errors.Error uu____7460 in
          raise uu____7459 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____7472 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____7480 =
            let uu____7481 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____7481 in
          if uu____7480 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7485),uu____7486,uu____7487) ->
              ((let uu____7498 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____7498
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____7501 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____7501
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7505 ->
              let uu____7510 =
                let uu____7511 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____7511 in
              if uu____7510 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7515 ->
              let uu____7519 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____7519 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7522 ->
              let uu____7525 =
                let uu____7526 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____7526 in
              if uu____7525 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7530 ->
              let uu____7531 =
                let uu____7532 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7532 in
              if uu____7531 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7536 ->
              let uu____7537 =
                let uu____7538 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____7538 in
              if uu____7537 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7542 ->
              let uu____7549 =
                let uu____7550 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____7550 in
              if uu____7549 then err'1 () else ()
          | uu____7554 -> ()))
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
                          let uu____7611 =
                            let uu____7614 =
                              let uu____7615 =
                                let uu____7620 =
                                  let uu____7621 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7621 in
                                (uu____7620, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____7615 in
                            FStar_Syntax_Syntax.mk uu____7614 in
                          uu____7611 None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7647  ->
                                  match uu____7647 with
                                  | (x,imp) ->
                                      let uu____7654 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____7654, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p in
                      let unrefined_arg_binder =
                        let uu____7658 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____7658 in
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
                             let uu____7667 =
                               let uu____7668 =
                                 let uu____7669 =
                                   let uu____7670 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____7671 =
                                     let uu____7672 =
                                       let uu____7673 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7673 in
                                     [uu____7672] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7670
                                     uu____7671 in
                                 uu____7669 None p in
                               FStar_Syntax_Util.b2t uu____7668 in
                             FStar_Syntax_Util.refine x uu____7667 in
                           let uu____7678 =
                             let uu___149_7679 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___149_7679.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___149_7679.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____7678) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____7689 =
                          FStar_List.map
                            (fun uu____7699  ->
                               match uu____7699 with
                               | (x,uu____7706) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps in
                        FStar_List.append uu____7689 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7730  ->
                                match uu____7730 with
                                | (x,uu____7737) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag)))) in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid in
                           let no_decl = false in
                           let only_decl =
                             (let uu____7746 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7746)
                               ||
                               (let uu____7747 =
                                  let uu____7748 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____7748.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____7747) in
                           let quals =
                             let uu____7751 =
                               let uu____7753 =
                                 let uu____7755 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____7755
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____7758 =
                                 FStar_List.filter
                                   (fun uu___112_7760  ->
                                      match uu___112_7760 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7761 -> false) iquals in
                               FStar_List.append uu____7753 uu____7758 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7751 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____7774 =
                                 let uu____7775 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7775 in
                               FStar_Syntax_Syntax.mk_Total uu____7774 in
                             let uu____7776 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7776 in
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
                           (let uu____7779 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____7779
                            then
                              let uu____7780 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7780
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
                                             fun uu____7808  ->
                                               match uu____7808 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7824 =
                                                       let uu____7827 =
                                                         let uu____7828 =
                                                           let uu____7833 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____7833,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7828 in
                                                       pos uu____7827 in
                                                     (uu____7824, b)
                                                   else
                                                     (let uu____7837 =
                                                        let uu____7840 =
                                                          let uu____7841 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7841 in
                                                        pos uu____7840 in
                                                      (uu____7837, b)))) in
                                   let pat_true =
                                     let uu____7853 =
                                       let uu____7856 =
                                         let uu____7857 =
                                           let uu____7865 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq) in
                                           (uu____7865, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7857 in
                                       pos uu____7856 in
                                     (uu____7853, None,
                                       FStar_Syntax_Const.exp_true_bool) in
                                   let pat_false =
                                     let uu____7887 =
                                       let uu____7890 =
                                         let uu____7891 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7891 in
                                       pos uu____7890 in
                                     (uu____7887, None,
                                       FStar_Syntax_Const.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (fst unrefined_arg_binder) in
                                   let uu____7900 =
                                     let uu____7903 =
                                       let uu____7904 =
                                         let uu____7920 =
                                           let uu____7922 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____7923 =
                                             let uu____7925 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____7925] in
                                           uu____7922 :: uu____7923 in
                                         (arg_exp, uu____7920) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7904 in
                                     FStar_Syntax_Syntax.mk uu____7903 in
                                   uu____7900 None p) in
                              let dd =
                                let uu____7936 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____7936
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
                                let uu____7948 =
                                  let uu____7951 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None in
                                  FStar_Util.Inr uu____7951 in
                                let uu____7952 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7948;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7952
                                } in
                              let impl =
                                let uu____7956 =
                                  let uu____7957 =
                                    let uu____7963 =
                                      let uu____7965 =
                                        let uu____7966 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____7966
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____7965] in
                                    ((false, [lb]), uu____7963, []) in
                                  FStar_Syntax_Syntax.Sig_let uu____7957 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____7956;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta
                                } in
                              (let uu____7981 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____7981
                               then
                                 let uu____7982 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7982
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
                                fun uu____8002  ->
                                  match uu____8002 with
                                  | (a,uu____8006) ->
                                      let uu____8007 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____8007 with
                                       | (field_name,uu____8011) ->
                                           let field_proj_tm =
                                             let uu____8013 =
                                               let uu____8014 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8014 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8013 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg] None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____8028 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8037  ->
                                    match uu____8037 with
                                    | (x,uu____8042) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____8044 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____8044 with
                                         | (field_name,uu____8049) ->
                                             let t =
                                               let uu____8051 =
                                                 let uu____8052 =
                                                   let uu____8055 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8055 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8052 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8051 in
                                             let only_decl =
                                               ((let uu____8057 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____8057)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____8058 =
                                                    let uu____8059 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____8059.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8058) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8069 =
                                                   FStar_List.filter
                                                     (fun uu___113_8071  ->
                                                        match uu___113_8071
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8072 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8069
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___114_8080  ->
                                                         match uu___114_8080
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____8081 ->
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
                                             ((let uu____8084 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____8084
                                               then
                                                 let uu____8085 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8085
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
                                                           fun uu____8112  ->
                                                             match uu____8112
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____8128
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____8128,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8140
                                                                    =
                                                                    let uu____8143
                                                                    =
                                                                    let uu____8144
                                                                    =
                                                                    let uu____8149
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____8149,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8144 in
                                                                    pos
                                                                    uu____8143 in
                                                                    (uu____8140,
                                                                    b))
                                                                   else
                                                                    (let uu____8153
                                                                    =
                                                                    let uu____8156
                                                                    =
                                                                    let uu____8157
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8157 in
                                                                    pos
                                                                    uu____8156 in
                                                                    (uu____8153,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____8169 =
                                                     let uu____8172 =
                                                       let uu____8173 =
                                                         let uu____8181 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq) in
                                                         (uu____8181,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8173 in
                                                     pos uu____8172 in
                                                   let uu____8187 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____8169, None,
                                                     uu____8187) in
                                                 let body =
                                                   let uu____8198 =
                                                     let uu____8201 =
                                                       let uu____8202 =
                                                         let uu____8218 =
                                                           let uu____8220 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____8220] in
                                                         (arg_exp,
                                                           uu____8218) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8202 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8201 in
                                                   uu____8198 None p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None in
                                                 let dd =
                                                   let uu____8237 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____8237
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
                                                   let uu____8243 =
                                                     let uu____8246 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None in
                                                     FStar_Util.Inr
                                                       uu____8246 in
                                                   let uu____8247 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8243;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8247
                                                   } in
                                                 let impl =
                                                   let uu____8251 =
                                                     let uu____8252 =
                                                       let uu____8258 =
                                                         let uu____8260 =
                                                           let uu____8261 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____8261
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____8260] in
                                                       ((false, [lb]),
                                                         uu____8258, []) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8252 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8251;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta
                                                   } in
                                                 (let uu____8276 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____8276
                                                  then
                                                    let uu____8277 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8277
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____8028 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8307) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____8310 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____8310 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____8323 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____8323 with
                    | (formals,uu____8333) ->
                        let uu____8344 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8357 =
                                   let uu____8358 =
                                     let uu____8359 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____8359 in
                                   FStar_Ident.lid_equals typ_lid uu____8358 in
                                 if uu____8357
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8369,uvs',tps,typ0,uu____8373,constrs)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8386 -> failwith "Impossible"
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
                        (match uu____8344 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____8428 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____8428 with
                              | (indices,uu____8438) ->
                                  let refine_domain =
                                    let uu____8450 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___115_8452  ->
                                              match uu___115_8452 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8453 -> true
                                              | uu____8458 -> false)) in
                                    if uu____8450
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___116_8465 =
                                      match uu___116_8465 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8467,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8474 -> None in
                                    let uu____8475 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____8475 with
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
                                    let uu____8483 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____8483 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8514  ->
                                               fun uu____8515  ->
                                                 match (uu____8514,
                                                         uu____8515)
                                                 with
                                                 | ((x,uu____8525),(x',uu____8527))
                                                     ->
                                                     let uu____8532 =
                                                       let uu____8537 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____8537) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8532) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8538 -> []