open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____19 = FStar_TypeChecker_Env.get_range env in
      let uu____20 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____19 uu____20
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____25 =
      let uu____26 = FStar_Syntax_Subst.compress t in
      uu____26.FStar_Syntax_Syntax.n in
    match uu____25 with
    | FStar_Syntax_Syntax.Tm_type uu____29 -> true
    | uu____30 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____41 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____41
      (FStar_List.filter
         (fun uu____55  ->
            match uu____55 with
            | (x,uu____61) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____75 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____77 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____77) in
        if uu____75
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____79 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____79 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____88 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____88
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___122_98  ->
    match uu___122_98 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____100);
        FStar_Syntax_Syntax.pos = uu____101;
        FStar_Syntax_Syntax.vars = uu____102;_} -> uv
    | uu____129 -> failwith "Impossible"
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
          let uu____158 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____158 with
          | FStar_Pervasives_Native.Some (uu____181::(tm,uu____183)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____235 ->
              let uu____246 = new_uvar_aux env k in
              (match uu____246 with
               | (t,u) ->
                   let g =
                     let uu___141_266 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____267 =
                       let uu____282 =
                         let uu____295 = as_uvar u in
                         (reason, env, uu____295, t, k, r) in
                       [uu____282] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___141_266.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_266.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_266.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____267
                     } in
                   let uu____320 =
                     let uu____327 =
                       let uu____332 = as_uvar u in (uu____332, r) in
                     [uu____327] in
                   (t, uu____320, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____362 =
        let uu____363 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____363 in
      if uu____362
      then
        let us =
          let uu____369 =
            let uu____372 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____390  ->
                 match uu____390 with
                 | (x,uu____396) -> FStar_Syntax_Print.uvar_to_string x)
              uu____372 in
          FStar_All.pipe_right uu____369 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____403 =
            let uu____404 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____404 in
          FStar_Errors.err r uu____403);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____419  ->
      match uu____419 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____429;
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
                   let uu____475 =
                     let uu____476 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____476.FStar_Syntax_Syntax.n in
                   match uu____475 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____483 = FStar_Syntax_Util.type_u () in
                       (match uu____483 with
                        | (k,uu____493) ->
                            let t2 =
                              let uu____495 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____495
                                FStar_Pervasives_Native.fst in
                            ((let uu___142_505 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___142_505.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___142_505.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____506 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____543) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____550) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____613) ->
                       let uu____634 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____694  ->
                                 fun uu____695  ->
                                   match (uu____694, uu____695) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____773 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____773 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____634 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____885 = aux must_check_ty1 scope body in
                            (match uu____885 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____914 =
                                         FStar_Options.ml_ish () in
                                       if uu____914
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____921 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____921
                                   then
                                     let uu____922 =
                                       FStar_Range.string_of_range r in
                                     let uu____923 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____924 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____922 uu____923 uu____924
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____934 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____948 =
                            let uu____953 =
                              let uu____954 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____954
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____953 in
                          (uu____948, false)) in
                 let uu____967 =
                   let uu____976 = t_binders env in aux false uu____976 e in
                 match uu____967 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1001 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____1001
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1005 =
                                let uu____1006 =
                                  let uu____1011 =
                                    let uu____1012 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____1012 in
                                  (uu____1011, rng) in
                                FStar_Errors.Error uu____1006 in
                              FStar_Exn.raise uu____1005)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1020 ->
               let uu____1021 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1021 with
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
                match c with
                | FStar_Const.Const_int
                    (repr,FStar_Pervasives_Native.Some sw) ->
                    FStar_ToSyntax_ToSyntax.desugar_machine_integer
                      env1.FStar_TypeChecker_Env.dsenv repr sw
                      p1.FStar_Syntax_Syntax.p
                | uu____1128 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1136) ->
              let uu____1141 = FStar_Syntax_Util.type_u () in
              (match uu____1141 with
               | (k,uu____1165) ->
                   let t = new_uvar env1 k in
                   let x1 =
                     let uu___143_1168 = x in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___143_1168.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___143_1168.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     } in
                   let uu____1169 =
                     let uu____1174 = FStar_TypeChecker_Env.all_binders env1 in
                     FStar_TypeChecker_Rel.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____1174 t in
                   (match uu____1169 with
                    | (e,u) ->
                        let p2 =
                          let uu___144_1198 = p1 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.p =
                              (uu___144_1198.FStar_Syntax_Syntax.p)
                          } in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1208 = FStar_Syntax_Util.type_u () in
              (match uu____1208 with
               | (t,uu____1232) ->
                   let x1 =
                     let uu___145_1234 = x in
                     let uu____1235 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___145_1234.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___145_1234.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1235
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
              let uu____1252 = FStar_Syntax_Util.type_u () in
              (match uu____1252 with
               | (t,uu____1276) ->
                   let x1 =
                     let uu___146_1278 = x in
                     let uu____1279 = new_uvar env1 t in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___146_1278.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___146_1278.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____1279
                     } in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1312 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1439  ->
                        fun uu____1440  ->
                          match (uu____1439, uu____1440) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1629 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2 in
                              (match uu____1629 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], [])) in
              (match uu____1312 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1827 =
                       let uu____1830 =
                         let uu____1831 =
                           let uu____1838 =
                             let uu____1841 =
                               let uu____1842 =
                                 FStar_Syntax_Syntax.fv_to_tm fv in
                               let uu____1843 =
                                 FStar_All.pipe_right args FStar_List.rev in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1842
                                 uu____1843 in
                             uu____1841 FStar_Pervasives_Native.None
                               p1.FStar_Syntax_Syntax.p in
                           (uu____1838,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app)) in
                         FStar_Syntax_Syntax.Tm_meta uu____1831 in
                       FStar_Syntax_Syntax.mk uu____1830 in
                     uu____1827 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1855 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1866 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1877 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1855, uu____1866, uu____1877, env2, e,
                     (let uu___147_1899 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___147_1899.FStar_Syntax_Syntax.p)
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
                  (fun uu____1983  ->
                     match uu____1983 with
                     | (p2,imp) ->
                         let uu____2002 = elaborate_pat env1 p2 in
                         (uu____2002, imp)) pats in
              let uu____2007 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              (match uu____2007 with
               | (uu____2014,t) ->
                   let uu____2016 = FStar_Syntax_Util.arrow_formals t in
                   (match uu____2016 with
                    | (f,uu____2032) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____2154::uu____2155) ->
                              FStar_Exn.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____2206::uu____2207,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____2285  ->
                                      match uu____2285 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____2312 =
                                                   let uu____2315 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1 in
                                                   FStar_Pervasives_Native.Some
                                                     uu____2315 in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____2312
                                                   FStar_Syntax_Syntax.tun in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                               let uu____2317 =
                                                 maybe_dot inaccessible a r in
                                               (uu____2317, true)
                                           | uu____2322 ->
                                               let uu____2325 =
                                                 let uu____2326 =
                                                   let uu____2331 =
                                                     let uu____2332 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2332 in
                                                   (uu____2331,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                 FStar_Errors.Error
                                                   uu____2326 in
                                               FStar_Exn.raise uu____2325)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____2406,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____2407))
                                   when p_imp ->
                                   let uu____2410 = aux formals' pats' in
                                   (p2, true) :: uu____2410
                               | (uu____2427,FStar_Pervasives_Native.Some
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
                                   let uu____2435 = aux formals' pats2 in
                                   (p3, true) :: uu____2435
                               | (uu____2452,imp) ->
                                   let uu____2458 =
                                     let uu____2465 =
                                       FStar_Syntax_Syntax.is_implicit imp in
                                     (p2, uu____2465) in
                                   let uu____2468 = aux formals' pats' in
                                   uu____2458 :: uu____2468) in
                        let uu___148_2483 = p1 in
                        let uu____2486 =
                          let uu____2487 =
                            let uu____2500 = aux f pats1 in (fv, uu____2500) in
                          FStar_Syntax_Syntax.Pat_cons uu____2487 in
                        {
                          FStar_Syntax_Syntax.v = uu____2486;
                          FStar_Syntax_Syntax.p =
                            (uu___148_2483.FStar_Syntax_Syntax.p)
                        }))
          | uu____2517 -> p1 in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____2551 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
          match uu____2551 with
          | (b,a,w,env2,arg,p3) ->
              let uu____2604 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____2604 with
               | FStar_Pervasives_Native.Some x ->
                   let uu____2628 =
                     let uu____2629 =
                       let uu____2634 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                       (uu____2634, (p3.FStar_Syntax_Syntax.p)) in
                     FStar_Errors.Error uu____2629 in
                   FStar_Exn.raise uu____2628
               | uu____2651 -> (b, a, w, arg, p3)) in
        let uu____2660 = one_pat true env p in
        match uu____2660 with
        | (b,uu____2686,uu____2687,tm,p1) -> (b, tm, p1)
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
          | (uu____2735,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2737)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2742,uu____2743) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2747 =
                    let uu____2748 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2749 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2748 uu____2749 in
                  failwith uu____2747)
               else ();
               (let uu____2752 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2752
                then
                  let uu____2753 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2754 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2753
                    uu____2754
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___149_2758 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___149_2758.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___149_2758.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2762 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2762
                then
                  let uu____2763 =
                    let uu____2764 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2765 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2764 uu____2765 in
                  failwith uu____2763
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___150_2769 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___150_2769.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___150_2769.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2771),uu____2772) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2794 =
                  let uu____2795 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2795 in
                if uu____2794
                then
                  let uu____2796 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2796
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2815;
                FStar_Syntax_Syntax.vars = uu____2816;_},args))
              ->
              ((let uu____2855 =
                  let uu____2856 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2856 Prims.op_Negation in
                if uu____2855
                then
                  let uu____2857 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2857
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2993)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3068) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3105) ->
                           let pat =
                             let uu____3127 = aux argpat e2 in
                             let uu____3128 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3127, uu____3128) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3133 ->
                      let uu____3156 =
                        let uu____3157 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3158 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3157 uu____3158 in
                      failwith uu____3156 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3170;
                     FStar_Syntax_Syntax.vars = uu____3171;_},uu____3172);
                FStar_Syntax_Syntax.pos = uu____3173;
                FStar_Syntax_Syntax.vars = uu____3174;_},args))
              ->
              ((let uu____3217 =
                  let uu____3218 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3218 Prims.op_Negation in
                if uu____3217
                then
                  let uu____3219 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3219
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3355)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3430) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3467) ->
                           let pat =
                             let uu____3489 = aux argpat e2 in
                             let uu____3490 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3489, uu____3490) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3495 ->
                      let uu____3518 =
                        let uu____3519 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3520 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3519 uu____3520 in
                      failwith uu____3518 in
                match_args [] args argpats))
          | uu____3529 ->
              let uu____3534 =
                let uu____3535 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3536 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3537 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3535 uu____3536 uu____3537 in
              failwith uu____3534 in
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
    let pat_as_arg uu____3575 =
      match uu____3575 with
      | (p,i) ->
          let uu____3592 = decorated_pattern_as_term p in
          (match uu____3592 with
           | (vars,te) ->
               let uu____3615 =
                 let uu____3620 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3620) in
               (vars, uu____3615)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3634 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3634)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3638 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3638)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3642 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3642)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3663 =
          let uu____3678 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3678 FStar_List.unzip in
        (match uu____3663 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3788 =
               let uu____3789 =
                 let uu____3790 =
                   let uu____3805 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3805, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3790 in
               mk1 uu____3789 in
             (vars1, uu____3788))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3846)::[] -> wp
      | uu____3863 ->
          let uu____3872 =
            let uu____3873 =
              let uu____3874 =
                FStar_List.map
                  (fun uu____3884  ->
                     match uu____3884 with
                     | (x,uu____3890) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3874 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3873 in
          failwith uu____3872 in
    let uu____3895 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3895, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3912 = destruct_comp c in
        match uu____3912 with
        | (u,uu____3920,wp) ->
            let uu____3922 =
              let uu____3931 =
                let uu____3932 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____3932 in
              [uu____3931] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3922;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3945 =
          let uu____3952 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____3953 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____3952 uu____3953 in
        match uu____3945 with | (m,uu____3955,uu____3956) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3969 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____3969
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
        let uu____4009 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4009 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4046 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4046 with
             | (a,kwp) ->
                 let uu____4077 = destruct_comp m1 in
                 let uu____4084 = destruct_comp m2 in
                 ((md, a, kwp), uu____4077, uu____4084))
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
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____4155 =
              let uu____4156 =
                let uu____4165 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4165] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4156;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4155
let mk_comp:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
      let uu___151_4215 = lc in
      let uu____4216 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___151_4215.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4216;
        FStar_Syntax_Syntax.cflags =
          (uu___151_4215.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4221  ->
             let uu____4222 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4222)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4227 =
      let uu____4228 = FStar_Syntax_Subst.compress t in
      uu____4228.FStar_Syntax_Syntax.n in
    match uu____4227 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4231 -> true
    | uu____4244 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4261 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4261
        then c
        else
          (let uu____4263 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4263
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4302 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4302] in
                       let us =
                         let uu____4306 =
                           let uu____4309 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4309] in
                         u_res :: uu____4306 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4313 =
                         let uu____4314 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4315 =
                           let uu____4316 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4317 =
                             let uu____4320 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4321 =
                               let uu____4324 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4324] in
                             uu____4320 :: uu____4321 in
                           uu____4316 :: uu____4317 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4314 uu____4315 in
                       uu____4313 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4328 = destruct_comp c1 in
              match uu____4328 with
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
        let close1 uu____4359 =
          let uu____4360 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4360 in
        let uu___152_4361 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___152_4361.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___152_4361.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___152_4361.FStar_Syntax_Syntax.cflags);
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
          let uu____4375 =
            let uu____4376 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4376 in
          if uu____4375
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4381 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4381
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4383 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4383 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____4391 =
                        let uu____4392 =
                          let uu____4393 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____4394 =
                            let uu____4395 = FStar_Syntax_Syntax.as_arg t in
                            let uu____4396 =
                              let uu____4399 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____4399] in
                            uu____4395 :: uu____4396 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4393 uu____4394 in
                        uu____4392 FStar_Pervasives_Native.None
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.NoFullNorm] env
                        uu____4391) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____4403 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4403
         then
           let uu____4404 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4405 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4406 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4404
             uu____4405 uu____4406
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
          fun uu____4429  ->
            match uu____4429 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4442 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4442
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4445 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4447 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4448 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4445 uu____4447 bstr uu____4448
                  else ());
                 (let bind_it uu____4453 =
                    let uu____4454 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4454
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4464 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4464
                        then
                          let uu____4465 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4467 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4468 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4469 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4470 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4465 uu____4467 uu____4468 uu____4469
                            uu____4470
                        else ());
                       (let try_simplify uu____4485 =
                          let aux uu____4499 =
                            let uu____4500 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4500
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4529 ->
                                  let uu____4530 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4530
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4557 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4557
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4613 =
                                  let uu____4618 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4618, reason) in
                                FStar_Util.Inl uu____4613
                            | uu____4623 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4642 =
                              let uu____4643 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4643.FStar_Syntax_Syntax.n in
                            match uu____4642 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4647) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4653 -> c in
                          let uu____4654 =
                            let uu____4655 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4655 in
                          if uu____4654
                          then
                            let uu____4668 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4668
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4688 =
                                  let uu____4689 =
                                    let uu____4694 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4694) in
                                  FStar_Errors.Error uu____4689 in
                                FStar_Exn.raise uu____4688))
                          else
                            (let uu____4706 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4706
                             then subst_c2 "both total"
                             else
                               (let uu____4718 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4718
                                then
                                  let uu____4729 =
                                    let uu____4734 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4734, "both gtot") in
                                  FStar_Util.Inl uu____4729
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4760 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4762 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4762) in
                                       if uu____4760
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___153_4775 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___153_4775.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___153_4775.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4776 =
                                           let uu____4781 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4781, "c1 Tot") in
                                         FStar_Util.Inl uu____4776
                                       else aux ()
                                   | uu____4787 -> aux ()))) in
                        let uu____4796 = try_simplify () in
                        match uu____4796 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4820 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4820
                              then
                                let uu____4821 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4822 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4823 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4821 uu____4822 uu____4823
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4832 = lift_and_destruct env c1 c2 in
                            (match uu____4832 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4889 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4889]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4891 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4891] in
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
                                   let uu____4904 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4905 =
                                     let uu____4908 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4909 =
                                       let uu____4912 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4913 =
                                         let uu____4916 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4917 =
                                           let uu____4920 =
                                             let uu____4921 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4921 in
                                           [uu____4920] in
                                         uu____4916 :: uu____4917 in
                                       uu____4912 :: uu____4913 in
                                     uu____4908 :: uu____4909 in
                                   uu____4904 :: uu____4905 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4926 =
                                     let uu____4927 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4927
                                       wp_args in
                                   uu____4926 FStar_Pervasives_Native.None
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
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
              let uu____4974 =
                let uu____4975 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4975 in
              if uu____4974
              then f
              else (let uu____4977 = reason1 () in label uu____4977 r f)
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
            let uu___154_4991 = g in
            let uu____4992 =
              let uu____4993 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4993 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4992;
              FStar_TypeChecker_Env.deferred =
                (uu___154_4991.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___154_4991.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___154_4991.FStar_TypeChecker_Env.implicits)
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
      | uu____5005 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5027 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5031 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5031
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5038 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5038
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5043 = destruct_comp c1 in
                    match uu____5043 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5059 =
                            let uu____5060 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5061 =
                              let uu____5062 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5063 =
                                let uu____5066 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5067 =
                                  let uu____5070 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5070] in
                                uu____5066 :: uu____5067 in
                              uu____5062 :: uu____5063 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5060
                              uu____5061 in
                          uu____5059 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___155_5073 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___155_5073.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___155_5073.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___155_5073.FStar_Syntax_Syntax.cflags);
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
            let uu____5111 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5111
            then (lc, g0)
            else
              ((let uu____5118 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5118
                then
                  let uu____5119 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5120 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5119 uu____5120
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___123_5130  ->
                          match uu___123_5130 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5133 -> [])) in
                let strengthen uu____5139 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5147 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5147 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5154 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5156 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5156) in
                           if uu____5154
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5163 =
                                 let uu____5164 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5164 in
                               FStar_Syntax_Util.comp_set_flags uu____5163
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5170 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5170
                           then
                             let uu____5171 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5172 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5171 uu____5172
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5175 = destruct_comp c2 in
                           match uu____5175 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5191 =
                                   let uu____5192 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5193 =
                                     let uu____5194 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5195 =
                                       let uu____5198 =
                                         let uu____5199 =
                                           let uu____5200 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5200 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5199 in
                                       let uu____5201 =
                                         let uu____5204 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5204] in
                                       uu____5198 :: uu____5201 in
                                     uu____5194 :: uu____5195 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5192
                                     uu____5193 in
                                 uu____5191 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5208 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5208
                                 then
                                   let uu____5209 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5209
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5212 =
                  let uu___156_5213 = lc in
                  let uu____5214 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5215 =
                    let uu____5218 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5220 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5220) in
                    if uu____5218 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5214;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___156_5213.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5215;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5212,
                  (let uu___157_5225 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___157_5225.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___157_5225.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___157_5225.FStar_TypeChecker_Env.implicits)
                   }))))
let add_equality_to_post_condition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun comp  ->
      fun res_t  ->
        let md_pure =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid in
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let y = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
        let uu____5243 =
          let uu____5248 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5249 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5248, uu____5249) in
        match uu____5243 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5258 =
                let uu____5259 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5260 =
                  let uu____5261 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5262 =
                    let uu____5265 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5265] in
                  uu____5261 :: uu____5262 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5259 uu____5260 in
              uu____5258 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5271 =
                let uu____5272 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5273 =
                  let uu____5274 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5275 =
                    let uu____5278 =
                      let uu____5279 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5279 in
                    let uu____5280 =
                      let uu____5283 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5283] in
                    uu____5278 :: uu____5280 in
                  uu____5274 :: uu____5275 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5272 uu____5273 in
              uu____5271 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5289 =
                let uu____5290 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5291 =
                  let uu____5292 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5293 =
                    let uu____5296 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5297 =
                      let uu____5300 =
                        let uu____5301 =
                          let uu____5302 =
                            let uu____5303 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5303] in
                          FStar_Syntax_Util.abs uu____5302 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5301 in
                      [uu____5300] in
                    uu____5296 :: uu____5297 in
                  uu____5292 :: uu____5293 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5290 uu____5291 in
              uu____5289 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5310 = FStar_TypeChecker_Env.get_range env in
              bind uu____5310 env FStar_Pervasives_Native.None
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
          let comp uu____5333 =
            let uu____5334 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5334
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5337 =
                 let uu____5362 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5363 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5362 uu____5363 in
               match uu____5337 with
               | ((md,uu____5365,uu____5366),(u_res_t,res_t,wp_then),
                  (uu____5370,uu____5371,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5409 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5410 =
                       let uu____5411 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5412 =
                         let uu____5413 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5414 =
                           let uu____5417 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5418 =
                             let uu____5421 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5422 =
                               let uu____5425 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5425] in
                             uu____5421 :: uu____5422 in
                           uu____5417 :: uu____5418 in
                         uu____5413 :: uu____5414 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5411 uu____5412 in
                     uu____5410 FStar_Pervasives_Native.None uu____5409 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5431 =
                     let uu____5432 = FStar_Options.split_cases () in
                     uu____5432 > (Prims.parse_int "0") in
                   if uu____5431
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5438 =
                          let uu____5439 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5440 =
                            let uu____5441 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5442 =
                              let uu____5445 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5445] in
                            uu____5441 :: uu____5442 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5439 uu____5440 in
                        uu____5438 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5448 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5448;
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
      let uu____5457 =
        let uu____5458 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5458 in
      FStar_Syntax_Syntax.fvar uu____5457 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5493  ->
                 match uu____5493 with
                 | (uu____5498,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5503 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5505 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5505
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5525 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5526 =
                 let uu____5527 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5528 =
                   let uu____5529 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5530 =
                     let uu____5533 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5534 =
                       let uu____5537 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5538 =
                         let uu____5541 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5541] in
                       uu____5537 :: uu____5538 in
                     uu____5533 :: uu____5534 in
                   uu____5529 :: uu____5530 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5527 uu____5528 in
               uu____5526 FStar_Pervasives_Native.None uu____5525 in
             let default_case =
               let post_k =
                 let uu____5548 =
                   let uu____5555 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5555] in
                 let uu____5556 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5548 uu____5556 in
               let kwp =
                 let uu____5562 =
                   let uu____5569 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5569] in
                 let uu____5570 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5562 uu____5570 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5575 =
                   let uu____5576 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5576] in
                 let uu____5577 =
                   let uu____5578 =
                     let uu____5581 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5581 in
                   let uu____5582 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5578 uu____5582 in
                 FStar_Syntax_Util.abs uu____5575 uu____5577
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
                 (fun uu____5606  ->
                    fun celse  ->
                      match uu____5606 with
                      | (g,cthen) ->
                          let uu____5614 =
                            let uu____5639 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5639 celse in
                          (match uu____5614 with
                           | ((md,uu____5641,uu____5642),(uu____5643,uu____5644,wp_then),
                              (uu____5646,uu____5647,wp_else)) ->
                               let uu____5667 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5667 []))
                 lcases default_case in
             let uu____5668 =
               let uu____5669 = FStar_Options.split_cases () in
               uu____5669 > (Prims.parse_int "0") in
             if uu____5668
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5673 = destruct_comp comp1 in
                match uu____5673 with
                | (uu____5680,uu____5681,wp) ->
                    let wp1 =
                      let uu____5686 =
                        let uu____5687 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5688 =
                          let uu____5689 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5690 =
                            let uu____5693 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5693] in
                          uu____5689 :: uu____5690 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5687 uu____5688 in
                      uu____5686 FStar_Pervasives_Native.None
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
          let uu____5711 =
            ((let uu____5714 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5714) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5716 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5716) in
          if uu____5711
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5725 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5729 =
            (let uu____5732 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____5732) || env.FStar_TypeChecker_Env.lax in
          if uu____5729
          then c
          else
            (let uu____5736 = FStar_Syntax_Util.is_partial_return c in
             if uu____5736
             then c
             else
               (let uu____5740 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5740
                then
                  let uu____5743 =
                    let uu____5744 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5744 in
                  (if uu____5743
                   then
                     let uu____5747 =
                       let uu____5748 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5749 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5748 uu____5749 in
                     failwith uu____5747
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5754 =
                        let uu____5755 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5755 in
                      if uu____5754
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___158_5760 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___158_5760.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___158_5760.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___158_5760.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5771 =
                       let uu____5774 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5774
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5771 in
                   let eq1 =
                     let uu____5778 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5778 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5780 =
                     let uu____5781 =
                       let uu____5786 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5786.FStar_Syntax_Syntax.comp in
                     uu____5781 () in
                   FStar_Syntax_Util.comp_set_flags uu____5780 flags))) in
        let uu___159_5789 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___159_5789.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___159_5789.FStar_Syntax_Syntax.res_typ);
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
          let uu____5818 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5818 with
          | FStar_Pervasives_Native.None  ->
              let uu____5827 =
                let uu____5828 =
                  let uu____5833 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5834 = FStar_TypeChecker_Env.get_range env in
                  (uu____5833, uu____5834) in
                FStar_Errors.Error uu____5828 in
              FStar_Exn.raise uu____5827
          | FStar_Pervasives_Native.Some g -> (e, c', g)
let maybe_coerce_bool_to_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1 in
            let uu____5871 =
              let uu____5872 = FStar_Syntax_Subst.compress t2 in
              uu____5872.FStar_Syntax_Syntax.n in
            match uu____5871 with
            | FStar_Syntax_Syntax.Tm_type uu____5875 -> true
            | uu____5876 -> false in
          let uu____5877 =
            let uu____5878 =
              FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ in
            uu____5878.FStar_Syntax_Syntax.n in
          match uu____5877 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5886 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5897 =
                  let uu____5898 =
                    let uu____5899 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5899 in
                  (FStar_Pervasives_Native.None, uu____5898) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5897 in
              let e1 =
                let uu____5909 =
                  let uu____5910 =
                    let uu____5911 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5911] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5910 in
                uu____5909 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5916 -> (e, lc)
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
              (let uu____5949 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5949 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5972 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5994 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5994, false)
            else
              (let uu____6000 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6000, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6011) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6020 =
                  let uu____6021 =
                    let uu____6026 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6026, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6021 in
                FStar_Exn.raise uu____6020
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___160_6036 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___160_6036.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___160_6036.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___160_6036.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6041 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6041 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___161_6049 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___161_6049.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___161_6049.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___161_6049.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___162_6052 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___162_6052.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___162_6052.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___162_6052.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6058 =
                     let uu____6059 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6059
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6064 =
                          let uu____6065 = FStar_Syntax_Subst.compress f1 in
                          uu____6065.FStar_Syntax_Syntax.n in
                        match uu____6064 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6070,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6072;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6073;_},uu____6074)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___163_6096 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___163_6096.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___163_6096.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___163_6096.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6097 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6102 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6102
                              then
                                let uu____6103 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6104 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6105 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6106 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6103 uu____6104 uu____6105 uu____6106
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6109 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6109 with
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
                                  let uu____6122 = destruct_comp ct in
                                  (match uu____6122 with
                                   | (u_t,uu____6132,uu____6133) ->
                                       let wp =
                                         let uu____6137 =
                                           let uu____6138 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6139 =
                                             let uu____6140 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6141 =
                                               let uu____6144 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6144] in
                                             uu____6140 :: uu____6141 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6138 uu____6139 in
                                         uu____6137
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6148 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6148 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6158 =
                                             let uu____6159 =
                                               let uu____6160 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6160] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6159 in
                                           uu____6158
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6164 =
                                         let uu____6169 =
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6182 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6183 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6169
                                           uu____6182 e cret uu____6183 in
                                       (match uu____6164 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___164_6189 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___164_6189.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___164_6189.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6191 =
                                                let uu____6192 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6192 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6191
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6203 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6203
                                              then
                                                let uu____6204 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6204
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___124_6214  ->
                             match uu___124_6214 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6217 -> [])) in
                   let lc1 =
                     let uu___165_6219 = lc in
                     let uu____6220 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6220;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___166_6222 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___166_6222.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___166_6222.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___166_6222.FStar_TypeChecker_Env.implicits)
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
        let uu____6247 =
          let uu____6248 =
            let uu____6249 =
              let uu____6250 =
                let uu____6251 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6251 in
              [uu____6250] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6249 in
          uu____6248 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6247 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6258 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6258
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6276 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6291 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6320)::(ens,uu____6322)::uu____6323 ->
                    let uu____6352 =
                      let uu____6355 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6355 in
                    let uu____6356 =
                      let uu____6357 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6357 in
                    (uu____6352, uu____6356)
                | uu____6360 ->
                    let uu____6369 =
                      let uu____6370 =
                        let uu____6375 =
                          let uu____6376 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6376 in
                        (uu____6375, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6370 in
                    FStar_Exn.raise uu____6369)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6392)::uu____6393 ->
                    let uu____6412 =
                      let uu____6417 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6417 in
                    (match uu____6412 with
                     | (us_r,uu____6449) ->
                         let uu____6450 =
                           let uu____6455 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6455 in
                         (match uu____6450 with
                          | (us_e,uu____6487) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6490 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6490
                                  us_r in
                              let as_ens =
                                let uu____6492 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6492
                                  us_e in
                              let req =
                                let uu____6496 =
                                  let uu____6497 =
                                    let uu____6498 =
                                      let uu____6509 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6509] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6498 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6497 in
                                uu____6496 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6527 =
                                  let uu____6528 =
                                    let uu____6529 =
                                      let uu____6540 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6540] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6529 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6528 in
                                uu____6527 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6555 =
                                let uu____6558 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6558 in
                              let uu____6559 =
                                let uu____6560 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6560 in
                              (uu____6555, uu____6559)))
                | uu____6563 -> failwith "Impossible"))
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
      (let uu____6591 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6591
       then
         let uu____6592 = FStar_Syntax_Print.term_to_string tm in
         let uu____6593 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6592 uu____6593
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
        (let uu____6614 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6614
         then
           let uu____6615 = FStar_Syntax_Print.term_to_string tm in
           let uu____6616 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6615
             uu____6616
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6622 =
      let uu____6623 =
        let uu____6624 = FStar_Syntax_Subst.compress t in
        uu____6624.FStar_Syntax_Syntax.n in
      match uu____6623 with
      | FStar_Syntax_Syntax.Tm_app uu____6627 -> false
      | uu____6642 -> true in
    if uu____6622
    then t
    else
      (let uu____6644 = FStar_Syntax_Util.head_and_args t in
       match uu____6644 with
       | (head1,args) ->
           let uu____6681 =
             let uu____6682 =
               let uu____6683 = FStar_Syntax_Subst.compress head1 in
               uu____6683.FStar_Syntax_Syntax.n in
             match uu____6682 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6686 -> false in
           if uu____6681
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6708 ->
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
             let uu____6748 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6748 with
             | (formals,uu____6762) ->
                 let n_implicits =
                   let uu____6780 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6856  ->
                             match uu____6856 with
                             | (uu____6863,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6780 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6994 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6994 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7018 =
                     let uu____7019 =
                       let uu____7024 =
                         let uu____7025 = FStar_Util.string_of_int n_expected in
                         let uu____7032 = FStar_Syntax_Print.term_to_string e in
                         let uu____7033 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7025 uu____7032 uu____7033 in
                       let uu____7040 = FStar_TypeChecker_Env.get_range env in
                       (uu____7024, uu____7040) in
                     FStar_Errors.Error uu____7019 in
                   FStar_Exn.raise uu____7018
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___125_7061 =
             match uu___125_7061 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7091 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7091 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_42,uu____7200) when
                          _0_42 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7243,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7276 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7276 with
                           | (v1,uu____7316,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7333 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7333 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7426 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7426)))
                      | (uu____7453,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7499 =
                      let uu____7526 = inst_n_binders t in
                      aux [] uu____7526 bs1 in
                    (match uu____7499 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7597) -> (e, torig, guard)
                          | (uu____7628,[]) when
                              let uu____7659 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7659 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7660 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7692 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7707 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7716 =
      let uu____7719 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7719
        (FStar_List.map
           (fun u  ->
              let uu____7729 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7729 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7716 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7748 = FStar_Util.set_is_empty x in
      if uu____7748
      then []
      else
        (let s =
           let uu____7755 =
             let uu____7758 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7758 in
           FStar_All.pipe_right uu____7755 FStar_Util.set_elements in
         (let uu____7766 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7766
          then
            let uu____7767 =
              let uu____7768 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7768 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7767
          else ());
         (let r =
            let uu____7775 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7775 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7790 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7790
                     then
                       let uu____7791 =
                         let uu____7792 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7792 in
                       let uu____7793 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7794 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7791 uu____7793 uu____7794
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
        let uu____7818 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7818 FStar_Util.fifo_set_elements in
      univnames1
let check_universe_generalization:
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____7853) -> generalized_univ_names
        | (uu____7860,[]) -> explicit_univ_names
        | uu____7867 ->
            let uu____7876 =
              let uu____7877 =
                let uu____7882 =
                  let uu____7883 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7883 in
                (uu____7882, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7877 in
            FStar_Exn.raise uu____7876
let generalize_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0 in
      let univnames1 = gather_free_univnames env t in
      let univs1 = FStar_Syntax_Free.univs t in
      (let uu____7902 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7902
       then
         let uu____7903 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7903
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7909 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7909
        then
          let uu____7910 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7910
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0 in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1 in (univs2, ts)))
let gen:
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple4 Prims.list
          FStar_Pervasives_Native.option
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____7975 =
          let uu____7976 =
            FStar_Util.for_all
              (fun uu____7989  ->
                 match uu____7989 with
                 | (uu____7998,uu____7999,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7976 in
        if uu____7975
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8037 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8037
              then
                let uu____8038 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8038
              else ());
             (let c1 =
                let uu____8041 = FStar_TypeChecker_Env.should_verify env in
                if uu____8041
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
              (let uu____8044 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8044
               then
                 let uu____8045 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8045
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8106 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8106 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8236 =
             match uu____8236 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8302 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8302
                   then
                     let uu____8303 =
                       let uu____8304 =
                         let uu____8307 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8307
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8304
                         (FStar_String.concat ", ") in
                     let uu____8334 =
                       let uu____8335 =
                         let uu____8338 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8338
                           (FStar_List.map
                              (fun uu____8366  ->
                                 match uu____8366 with
                                 | (u,t2) ->
                                     let uu____8373 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8374 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8373 uu____8374)) in
                       FStar_All.pipe_right uu____8335
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8303
                       uu____8334
                   else ());
                  (let univs2 =
                     let uu____8381 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8404  ->
                            match uu____8404 with
                            | (uu____8413,t2) ->
                                let uu____8415 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8415)
                       univs1 uu____8381 in
                   let uvs = gen_uvars uvt in
                   (let uu____8438 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8438
                    then
                      let uu____8439 =
                        let uu____8440 =
                          let uu____8443 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8443
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8440
                          (FStar_String.concat ", ") in
                      let uu____8470 =
                        let uu____8471 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8503  ->
                                  match uu____8503 with
                                  | (u,t2) ->
                                      let uu____8510 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8511 =
                                        FStar_Syntax_Print.term_to_string t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8510 uu____8511)) in
                        FStar_All.pipe_right uu____8471
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8439
                        uu____8470
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8541 =
             let uu____8574 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8574 in
           match uu____8541 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8688 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8688
                 then ()
                 else
                   (let uu____8690 = lec_hd in
                    match uu____8690 with
                    | (lb1,uu____8698,uu____8699) ->
                        let uu____8700 = lec2 in
                        (match uu____8700 with
                         | (lb2,uu____8708,uu____8709) ->
                             let msg =
                               let uu____8711 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8712 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8711 uu____8712 in
                             let uu____8713 =
                               let uu____8714 =
                                 let uu____8719 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8719) in
                               FStar_Errors.Error uu____8714 in
                             FStar_Exn.raise uu____8713)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8830  ->
                           match uu____8830 with
                           | (u,uu____8838) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8860  ->
                                       match uu____8860 with
                                       | (u',uu____8868) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8873 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8873
                 then ()
                 else
                   (let uu____8875 = lec_hd in
                    match uu____8875 with
                    | (lb1,uu____8883,uu____8884) ->
                        let uu____8885 = lec2 in
                        (match uu____8885 with
                         | (lb2,uu____8893,uu____8894) ->
                             let msg =
                               let uu____8896 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8897 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8896 uu____8897 in
                             let uu____8898 =
                               let uu____8899 =
                                 let uu____8904 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8904) in
                               FStar_Errors.Error uu____8899 in
                             FStar_Exn.raise uu____8898)) in
               let lecs1 =
                 let uu____8914 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8973 = univs_and_uvars_of_lec this_lec in
                        match uu____8973 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8914 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9151  ->
                         match uu____9151 with
                         | (u,k) ->
                             let uu____9164 = FStar_Syntax_Unionfind.find u in
                             (match uu____9164 with
                              | FStar_Pervasives_Native.Some uu____9173 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9180 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9184 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9184 with
                                   | (bs,kres) ->
                                       let a =
                                         let uu____9222 =
                                           let uu____9225 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           FStar_All.pipe_left
                                             (fun _0_43  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_43) uu____9225 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____9222 kres in
                                       let t =
                                         let uu____9229 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Util.abs bs uu____9229
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 kres)) in
                                       (FStar_Syntax_Util.set_uvar u t;
                                        (a,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag))))))) in
               let gen_univs1 = gen_univs env univs1 in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9317  ->
                         match uu____9317 with
                         | (lbname,e,c) ->
                             let uu____9353 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____9388 ->
                                   let uu____9403 = (e, c) in
                                   (match uu____9403 with
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
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____9430  ->
                                                   match uu____9430 with
                                                   | (x,uu____9438) ->
                                                       let uu____9443 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9443)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9453 =
                                                let uu____9454 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9454 in
                                              if uu____9453
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1 in
                                        let t =
                                          let uu____9462 =
                                            let uu____9463 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9463.FStar_Syntax_Syntax.n in
                                          match uu____9462 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9486 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9486 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9501 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9503 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9503)) in
                             (match uu____9353 with
                              | (e1,c1) -> (lbname, gen_univs1, e1, c1)))) in
               FStar_Pervasives_Native.Some ecs)
let generalize:
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____9591 = Obj.magic () in ());
        (let uu____9593 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9593
         then
           let uu____9594 =
             let uu____9595 =
               FStar_List.map
                 (fun uu____9608  ->
                    match uu____9608 with
                    | (lb,uu____9616,uu____9617) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9595 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9594
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9638  ->
                match uu____9638 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9663 = gen env is_rec lecs in
           match uu____9663 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9742  ->
                       match uu____9742 with | (l,t,c) -> (l, [], t, c)))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9790 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____9790
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9826  ->
                           match uu____9826 with
                           | (l,us,e,c) ->
                               let uu____9857 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____9858 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____9859 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____9860 =
                                 FStar_Syntax_Print.term_to_string e in
                               FStar_Util.print4
                                 "(%s) Generalized %s at type %s\n%s\n"
                                 uu____9857 uu____9858 uu____9859 uu____9860))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9892  ->
                match uu____9892 with
                | (l,generalized_univs,t,c) ->
                    let uu____9923 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____9923, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____9968 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____9968 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9974 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                     uu____9974) in
          let is_var e1 =
            let uu____9981 =
              let uu____9982 = FStar_Syntax_Subst.compress e1 in
              uu____9982.FStar_Syntax_Syntax.n in
            match uu____9981 with
            | FStar_Syntax_Syntax.Tm_name uu____9985 -> true
            | uu____9986 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___167_10002 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___167_10002.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___167_10002.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10003 -> e2 in
          let env2 =
            let uu___168_10005 = env1 in
            let uu____10006 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___168_10005.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___168_10005.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___168_10005.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___168_10005.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___168_10005.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___168_10005.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___168_10005.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___168_10005.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___168_10005.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___168_10005.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___168_10005.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___168_10005.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___168_10005.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___168_10005.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___168_10005.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10006;
              FStar_TypeChecker_Env.is_iface =
                (uu___168_10005.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___168_10005.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___168_10005.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___168_10005.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___168_10005.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___168_10005.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___168_10005.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___168_10005.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___168_10005.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___168_10005.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___168_10005.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___168_10005.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___168_10005.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___168_10005.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___168_10005.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___168_10005.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___168_10005.FStar_TypeChecker_Env.dsenv)
            } in
          let uu____10007 = check env2 t1 t2 in
          match uu____10007 with
          | FStar_Pervasives_Native.None  ->
              let uu____10014 =
                let uu____10015 =
                  let uu____10020 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10021 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10020, uu____10021) in
                FStar_Errors.Error uu____10015 in
              FStar_Exn.raise uu____10014
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10028 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10028
                then
                  let uu____10029 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10029
                else ());
               (let uu____10031 = decorate e t2 in (uu____10031, g)))
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
        let uu____10062 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10062
        then
          let uu____10067 = discharge g1 in
          let uu____10068 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10067, uu____10068)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10081 =
               let uu____10082 =
                 let uu____10083 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10083 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10082
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10081
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10085 = destruct_comp c1 in
           match uu____10085 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10102 = FStar_TypeChecker_Env.get_range env in
                 let uu____10103 =
                   let uu____10104 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10105 =
                     let uu____10106 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10107 =
                       let uu____10110 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10110] in
                     uu____10106 :: uu____10107 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10104 uu____10105 in
                 uu____10103 FStar_Pervasives_Native.None uu____10102 in
               ((let uu____10114 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10114
                 then
                   let uu____10115 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10115
                 else ());
                (let g2 =
                   let uu____10118 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10118 in
                 let uu____10119 = discharge g2 in
                 let uu____10120 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10119, uu____10120))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___126_10146 =
        match uu___126_10146 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10154)::[] -> f fst1
        | uu____10171 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10176 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10176
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_e e =
        let uu____10185 =
          let uu____10188 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10188 in
        FStar_All.pipe_right uu____10185
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_or_t t =
        let uu____10199 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10199
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49) in
      let short_op_ite uu___127_10213 =
        match uu___127_10213 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10221)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10240)::[] ->
            let uu____10269 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10269
              (fun _0_50  -> FStar_TypeChecker_Common.NonTrivial _0_50)
        | uu____10274 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10284 =
          let uu____10291 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10291) in
        let uu____10296 =
          let uu____10305 =
            let uu____10312 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10312) in
          let uu____10317 =
            let uu____10326 =
              let uu____10333 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10333) in
            let uu____10338 =
              let uu____10347 =
                let uu____10354 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10354) in
              let uu____10359 =
                let uu____10368 =
                  let uu____10375 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10375) in
                [uu____10368; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10347 :: uu____10359 in
            uu____10326 :: uu____10338 in
          uu____10305 :: uu____10317 in
        uu____10284 :: uu____10296 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10426 =
            FStar_Util.find_map table
              (fun uu____10439  ->
                 match uu____10439 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10456 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10456
                     else FStar_Pervasives_Native.None) in
          (match uu____10426 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10459 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10464 =
      let uu____10465 = FStar_Syntax_Util.un_uinst l in
      uu____10465.FStar_Syntax_Syntax.n in
    match uu____10464 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10469 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10495)::uu____10496 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10507 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10514,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10515))::uu____10516 -> bs
      | uu____10533 ->
          let uu____10534 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10534 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10538 =
                 let uu____10539 = FStar_Syntax_Subst.compress t in
                 uu____10539.FStar_Syntax_Syntax.n in
               (match uu____10538 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10543) ->
                    let uu____10560 =
                      FStar_Util.prefix_until
                        (fun uu___128_10600  ->
                           match uu___128_10600 with
                           | (uu____10607,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10608)) ->
                               false
                           | uu____10611 -> true) bs' in
                    (match uu____10560 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10646,uu____10647) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10719,uu____10720) ->
                         let uu____10793 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10811  ->
                                   match uu____10811 with
                                   | (x,uu____10819) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10793
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10866  ->
                                     match uu____10866 with
                                     | (x,i) ->
                                         let uu____10885 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10885, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10895 -> bs))
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
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
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
          let uu____10936 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____10936
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
let d: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s
let mk_toplevel_definition:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____10963 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____10963
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____10965 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____10965))
         else ());
        (let fv =
           let uu____10968 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10968
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
         let uu____10976 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___169_10982 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___169_10982.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___169_10982.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___169_10982.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___169_10982.FStar_Syntax_Syntax.sigattrs)
           }), uu____10976))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___129_10994 =
        match uu___129_10994 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10995 -> false in
      let reducibility uu___130_10999 =
        match uu___130_10999 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11000 -> false in
      let assumption uu___131_11004 =
        match uu___131_11004 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11005 -> false in
      let reification uu___132_11009 =
        match uu___132_11009 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11010 -> true
        | uu____11011 -> false in
      let inferred uu___133_11015 =
        match uu___133_11015 with
        | FStar_Syntax_Syntax.Discriminator uu____11016 -> true
        | FStar_Syntax_Syntax.Projector uu____11017 -> true
        | FStar_Syntax_Syntax.RecordType uu____11022 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11031 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11040 -> false in
      let has_eq uu___134_11044 =
        match uu___134_11044 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11045 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11105 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11110 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11114 =
        let uu____11115 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___135_11119  ->
                  match uu___135_11119 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11120 -> false)) in
        FStar_All.pipe_right uu____11115 Prims.op_Negation in
      if uu____11114
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11133 =
            let uu____11134 =
              let uu____11139 =
                let uu____11140 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11140 msg in
              (uu____11139, r) in
            FStar_Errors.Error uu____11134 in
          FStar_Exn.raise uu____11133 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11148 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11152 =
            let uu____11153 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11153 in
          if uu____11152 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11158),uu____11159) ->
              ((let uu____11175 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11175
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11179 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11179
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11185 ->
              let uu____11194 =
                let uu____11195 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11195 in
              if uu____11194 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11201 ->
              let uu____11208 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11208 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11212 ->
              let uu____11219 =
                let uu____11220 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11220 in
              if uu____11219 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11226 ->
              let uu____11227 =
                let uu____11228 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11228 in
              if uu____11227 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11234 ->
              let uu____11235 =
                let uu____11236 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11236 in
              if uu____11235 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11242 ->
              let uu____11255 =
                let uu____11256 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11256 in
              if uu____11255 then err'1 () else ()
          | uu____11262 -> ()))
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
                          let uu____11335 =
                            let uu____11338 =
                              let uu____11339 =
                                let uu____11346 =
                                  let uu____11347 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11347 in
                                (uu____11346, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11339 in
                            FStar_Syntax_Syntax.mk uu____11338 in
                          uu____11335 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11388  ->
                                  match uu____11388 with
                                  | (x,imp) ->
                                      let uu____11399 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11399, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11401 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11401 in
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
                             let uu____11410 =
                               let uu____11411 =
                                 let uu____11412 =
                                   let uu____11413 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11414 =
                                     let uu____11415 =
                                       let uu____11416 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11416 in
                                     [uu____11415] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11413
                                     uu____11414 in
                                 uu____11412 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11411 in
                             FStar_Syntax_Util.refine x uu____11410 in
                           let uu____11419 =
                             let uu___170_11420 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_11420.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___170_11420.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11419) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11435 =
                          FStar_List.map
                            (fun uu____11457  ->
                               match uu____11457 with
                               | (x,uu____11469) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11435 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11518  ->
                                match uu____11518 with
                                | (x,uu____11530) ->
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
                             (let uu____11544 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11544)
                               ||
                               (let uu____11546 =
                                  let uu____11547 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11547.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11546) in
                           let quals =
                             let uu____11551 =
                               let uu____11554 =
                                 let uu____11557 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11557
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11561 =
                                 FStar_List.filter
                                   (fun uu___136_11565  ->
                                      match uu___136_11565 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11566 -> false) iquals in
                               FStar_List.append uu____11554 uu____11561 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11551 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11587 =
                                 let uu____11588 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11588 in
                               FStar_Syntax_Syntax.mk_Total uu____11587 in
                             let uu____11589 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11589 in
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
                           (let uu____11592 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11592
                            then
                              let uu____11593 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11593
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
                                             fun uu____11646  ->
                                               match uu____11646 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11670 =
                                                       let uu____11673 =
                                                         let uu____11674 =
                                                           let uu____11681 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11681,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11674 in
                                                       pos uu____11673 in
                                                     (uu____11670, b)
                                                   else
                                                     (let uu____11685 =
                                                        let uu____11688 =
                                                          let uu____11689 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11689 in
                                                        pos uu____11688 in
                                                      (uu____11685, b)))) in
                                   let pat_true =
                                     let uu____11707 =
                                       let uu____11710 =
                                         let uu____11711 =
                                           let uu____11724 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11724, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11711 in
                                       pos uu____11710 in
                                     (uu____11707,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____11758 =
                                       let uu____11761 =
                                         let uu____11762 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____11762 in
                                       pos uu____11761 in
                                     (uu____11758,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____11774 =
                                     let uu____11777 =
                                       let uu____11778 =
                                         let uu____11801 =
                                           let uu____11804 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____11805 =
                                             let uu____11808 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____11808] in
                                           uu____11804 :: uu____11805 in
                                         (arg_exp, uu____11801) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11778 in
                                     FStar_Syntax_Syntax.mk uu____11777 in
                                   uu____11774 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____11815 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____11815
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
                                let uu____11823 =
                                  let uu____11828 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____11828 in
                                let uu____11829 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____11823;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____11829
                                } in
                              let impl =
                                let uu____11833 =
                                  let uu____11834 =
                                    let uu____11841 =
                                      let uu____11844 =
                                        let uu____11845 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____11845
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____11844] in
                                    ((false, [lb]), uu____11841) in
                                  FStar_Syntax_Syntax.Sig_let uu____11834 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____11833;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____11863 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____11863
                               then
                                 let uu____11864 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____11864
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
                                fun uu____11906  ->
                                  match uu____11906 with
                                  | (a,uu____11912) ->
                                      let uu____11913 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____11913 with
                                       | (field_name,uu____11919) ->
                                           let field_proj_tm =
                                             let uu____11921 =
                                               let uu____11922 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____11922 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____11921 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____11939 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____11971  ->
                                    match uu____11971 with
                                    | (x,uu____11979) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____11981 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____11981 with
                                         | (field_name,uu____11989) ->
                                             let t =
                                               let uu____11991 =
                                                 let uu____11992 =
                                                   let uu____11995 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____11995 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____11992 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____11991 in
                                             let only_decl =
                                               (let uu____11999 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____11999)
                                                 ||
                                                 (let uu____12001 =
                                                    let uu____12002 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12002.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12001) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12016 =
                                                   FStar_List.filter
                                                     (fun uu___137_12020  ->
                                                        match uu___137_12020
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12021 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12016
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___138_12034  ->
                                                         match uu___138_12034
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12035 ->
                                                             false)) in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1) in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute] in
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
                                                   = attrs
                                               } in
                                             ((let uu____12054 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12054
                                               then
                                                 let uu____12055 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12055
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
                                                           fun uu____12103 
                                                             ->
                                                             match uu____12103
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12127
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12127,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12143
                                                                    =
                                                                    let uu____12146
                                                                    =
                                                                    let uu____12147
                                                                    =
                                                                    let uu____12154
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12154,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12147 in
                                                                    pos
                                                                    uu____12146 in
                                                                    (uu____12143,
                                                                    b))
                                                                   else
                                                                    (let uu____12158
                                                                    =
                                                                    let uu____12161
                                                                    =
                                                                    let uu____12162
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12162 in
                                                                    pos
                                                                    uu____12161 in
                                                                    (uu____12158,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12178 =
                                                     let uu____12181 =
                                                       let uu____12182 =
                                                         let uu____12195 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12195,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12182 in
                                                     pos uu____12181 in
                                                   let uu____12204 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12178,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12204) in
                                                 let body =
                                                   let uu____12216 =
                                                     let uu____12219 =
                                                       let uu____12220 =
                                                         let uu____12243 =
                                                           let uu____12246 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12246] in
                                                         (arg_exp,
                                                           uu____12243) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12220 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12219 in
                                                   uu____12216
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12254 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12254
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
                                                   let uu____12261 =
                                                     let uu____12266 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12266 in
                                                   let uu____12267 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12261;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12267
                                                   } in
                                                 let impl =
                                                   let uu____12271 =
                                                     let uu____12272 =
                                                       let uu____12279 =
                                                         let uu____12282 =
                                                           let uu____12283 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12283
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12282] in
                                                       ((false, [lb]),
                                                         uu____12279) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12272 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12271;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   } in
                                                 (let uu____12301 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12301
                                                  then
                                                    let uu____12302 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12302
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____11939 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12346) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12351 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12351 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12373 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12373 with
                    | (formals,uu____12389) ->
                        let uu____12406 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12438 =
                                   let uu____12439 =
                                     let uu____12440 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12440 in
                                   FStar_Ident.lid_equals typ_lid uu____12439 in
                                 if uu____12438
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12459,uvs',tps,typ0,uu____12463,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12482 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor",
                                       (se.FStar_Syntax_Syntax.sigrng))) in
                        (match uu____12406 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12555 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12555 with
                              | (indices,uu____12571) ->
                                  let refine_domain =
                                    let uu____12589 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___139_12594  ->
                                              match uu___139_12594 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12595 -> true
                                              | uu____12604 -> false)) in
                                    if uu____12589
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___140_12612 =
                                      match uu___140_12612 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12615,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12627 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12628 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12628 with
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
                                    let uu____12639 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12639 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12704  ->
                                               fun uu____12705  ->
                                                 match (uu____12704,
                                                         uu____12705)
                                                 with
                                                 | ((x,uu____12723),(x',uu____12725))
                                                     ->
                                                     let uu____12734 =
                                                       let uu____12741 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12741) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12734) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12742 -> []