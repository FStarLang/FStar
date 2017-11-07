open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____17 = FStar_TypeChecker_Env.get_range env in
      let uu____18 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____17 uu____18
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____22 =
      let uu____23 = FStar_Syntax_Subst.compress t in
      uu____23.FStar_Syntax_Syntax.n in
    match uu____22 with
    | FStar_Syntax_Syntax.Tm_type uu____26 -> true
    | uu____27 -> false
let t_binders:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    let uu____37 = FStar_TypeChecker_Env.all_binders env in
    FStar_All.pipe_right uu____37
      (FStar_List.filter
         (fun uu____51  ->
            match uu____51 with
            | (x,uu____57) -> is_type x.FStar_Syntax_Syntax.sort))
let new_uvar_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____69 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____71 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____71) in
        if uu____69
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____73 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____73 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____80 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____80
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___326_89  ->
    match uu___326_89 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____91);
        FStar_Syntax_Syntax.pos = uu____92;
        FStar_Syntax_Syntax.vars = uu____93;_} -> uv
    | uu____120 -> failwith "Impossible"
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
          let uu____145 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____145 with
          | FStar_Pervasives_Native.Some (uu____168::(tm,uu____170)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____222 ->
              let uu____233 = new_uvar_aux env k in
              (match uu____233 with
               | (t,u) ->
                   let g =
                     let uu___345_253 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____254 =
                       let uu____269 =
                         let uu____282 = as_uvar u in
                         (reason, env, uu____282, t, k, r) in
                       [uu____269] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___345_253.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___345_253.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___345_253.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____254
                     } in
                   let uu____307 =
                     let uu____314 =
                       let uu____319 = as_uvar u in (uu____319, r) in
                     [uu____314] in
                   (t, uu____307, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____347 =
        let uu____348 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____348 in
      if uu____347
      then
        let us =
          let uu____354 =
            let uu____357 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____375  ->
                 match uu____375 with
                 | (x,uu____381) -> FStar_Syntax_Print.uvar_to_string x)
              uu____357 in
          FStar_All.pipe_right uu____354 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____388 =
            let uu____389 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____389 in
          FStar_Errors.err r uu____388);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____402  ->
      match uu____402 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____412;
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
                   let uu____458 =
                     let uu____459 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____459.FStar_Syntax_Syntax.n in
                   match uu____458 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____466 = FStar_Syntax_Util.type_u () in
                       (match uu____466 with
                        | (k,uu____476) ->
                            let t2 =
                              let uu____478 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____478
                                FStar_Pervasives_Native.fst in
                            ((let uu___346_488 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___346_488.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___346_488.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____489 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____526) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____533) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____596) ->
                       let uu____617 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____677  ->
                                 fun uu____678  ->
                                   match (uu____677, uu____678) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____756 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____756 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____617 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____868 = aux must_check_ty1 scope body in
                            (match uu____868 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____897 =
                                         FStar_Options.ml_ish () in
                                       if uu____897
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____904 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____904
                                   then
                                     let uu____905 =
                                       FStar_Range.string_of_range r in
                                     let uu____906 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____907 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____905 uu____906 uu____907
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____917 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____931 =
                            let uu____936 =
                              let uu____937 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____937
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____936 in
                          (uu____931, false)) in
                 let uu____950 =
                   let uu____959 = t_binders env in aux false uu____959 e in
                 match uu____950 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____984 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____984
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____988 =
                                let uu____989 =
                                  let uu____994 =
                                    let uu____995 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____995 in
                                  (uu____994, rng) in
                                FStar_Errors.Error uu____989 in
                              FStar_Exn.raise uu____988)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1003 ->
               let uu____1004 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1004 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
let pat_as_exp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_Syntax_Syntax.pat) FStar_Pervasives_Native.tuple3
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let t_x =
              let uu____1065 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
              match uu____1065 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1066;
                  FStar_Syntax_Syntax.vars = uu____1067;_} ->
                  let uu____1070 = FStar_Syntax_Util.type_u () in
                  (match uu____1070 with | (t,uu____1076) -> new_uvar env1 t)
              | t -> tc_annot env1 t in
            let uu___347_1078 = x in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___347_1078.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___347_1078.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = t_x
            } in
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
                  | uu____1143 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1151) ->
                let uu____1156 = FStar_Syntax_Util.type_u () in
                (match uu____1156 with
                 | (k,uu____1180) ->
                     let t = new_uvar env1 k in
                     let x1 =
                       let uu___348_1183 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___348_1183.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___348_1183.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       } in
                     let uu____1184 =
                       let uu____1189 =
                         FStar_TypeChecker_Env.all_binders env1 in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1189 t in
                     (match uu____1184 with
                      | (e,u) ->
                          let p2 =
                            let uu___349_1213 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___349_1213.FStar_Syntax_Syntax.p)
                            } in
                          ([], [], [], env1, e, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let x1 = check_bv env1 x in
                let env2 =
                  if allow_wc_dependence
                  then FStar_TypeChecker_Env.push_bv env1 x1
                  else env1 in
                let e =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                    FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([x1], [], [x1], env2, e, p1)
            | FStar_Syntax_Syntax.Pat_var x ->
                let x1 = check_bv env1 x in
                let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                let e =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                    FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([x1], [x1], [], env2, e, p1)
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1269 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1396  ->
                          fun uu____1397  ->
                            match (uu____1396, uu____1397) with
                            | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                                let uu____1586 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2 in
                                (match uu____1586 with
                                 | (b',a',w',env3,te,pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), ((pat, imp) :: pats1))))
                       ([], [], [], env1, [], [])) in
                (match uu____1269 with
                 | (b,a,w,env2,args,pats1) ->
                     let e =
                       let uu____1784 =
                         let uu____1787 =
                           let uu____1788 =
                             let uu____1795 =
                               let uu____1798 =
                                 let uu____1799 =
                                   FStar_Syntax_Syntax.fv_to_tm fv in
                                 let uu____1800 =
                                   FStar_All.pipe_right args FStar_List.rev in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1799
                                   uu____1800 in
                               uu____1798 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p in
                             (uu____1795,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app)) in
                           FStar_Syntax_Syntax.Tm_meta uu____1788 in
                         FStar_Syntax_Syntax.mk uu____1787 in
                       uu____1784 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     let uu____1812 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu____1823 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu____1834 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu____1812, uu____1823, uu____1834, env2, e,
                       (let uu___350_1856 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___350_1856.FStar_Syntax_Syntax.p)
                        }))) in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____1940  ->
                       match uu____1940 with
                       | (p2,imp) ->
                           let uu____1959 = elaborate_pat env1 p2 in
                           (uu____1959, imp)) pats in
                let uu____1964 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____1964 with
                 | (uu____1971,t) ->
                     let uu____1973 = FStar_Syntax_Util.arrow_formals t in
                     (match uu____1973 with
                      | (f,uu____1989) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2111::uu____2112) ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Too many pattern arguments",
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                            | (uu____2163::uu____2164,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2242  ->
                                        match uu____2242 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2269 =
                                                     let uu____2272 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2272 in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2269
                                                     FStar_Syntax_Syntax.tun in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                 let uu____2274 =
                                                   maybe_dot inaccessible a r in
                                                 (uu____2274, true)
                                             | uu____2279 ->
                                                 let uu____2282 =
                                                   let uu____2283 =
                                                     let uu____2288 =
                                                       let uu____2289 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.format1
                                                         "Insufficient pattern arguments (%s)"
                                                         uu____2289 in
                                                     (uu____2288,
                                                       (FStar_Ident.range_of_lid
                                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                   FStar_Errors.Error
                                                     uu____2283 in
                                                 FStar_Exn.raise uu____2282)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2363,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2364)) when p_imp ->
                                     let uu____2367 = aux formals' pats' in
                                     (p2, true) :: uu____2367
                                 | (uu____2384,FStar_Pervasives_Native.Some
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
                                     let uu____2392 = aux formals' pats2 in
                                     (p3, true) :: uu____2392
                                 | (uu____2409,imp) ->
                                     let uu____2415 =
                                       let uu____2422 =
                                         FStar_Syntax_Syntax.is_implicit imp in
                                       (p2, uu____2422) in
                                     let uu____2425 = aux formals' pats' in
                                     uu____2415 :: uu____2425) in
                          let uu___351_2440 = p1 in
                          let uu____2443 =
                            let uu____2444 =
                              let uu____2457 = aux f pats1 in
                              (fv, uu____2457) in
                            FStar_Syntax_Syntax.Pat_cons uu____2444 in
                          {
                            FStar_Syntax_Syntax.v = uu____2443;
                            FStar_Syntax_Syntax.p =
                              (uu___351_2440.FStar_Syntax_Syntax.p)
                          }))
            | uu____2474 -> p1 in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu____2508 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
            match uu____2508 with
            | (b,a,w,env2,arg,p3) ->
                let uu____2561 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu____2561 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2585 =
                       let uu____2586 =
                         let uu____2591 =
                           FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                         (uu____2591, (p3.FStar_Syntax_Syntax.p)) in
                       FStar_Errors.Error uu____2586 in
                     FStar_Exn.raise uu____2585
                 | uu____2608 -> (b, a, w, arg, p3)) in
          let uu____2617 = one_pat true env p in
          match uu____2617 with
          | (b,uu____2643,uu____2644,tm,p1) -> (b, tm, p1)
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
          | (uu____2689,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2691)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2696,uu____2697) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2701 =
                    let uu____2702 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2703 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2702 uu____2703 in
                  failwith uu____2701)
               else ();
               (let uu____2706 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2706
                then
                  let uu____2707 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2708 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2707
                    uu____2708
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___352_2712 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___352_2712.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___352_2712.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2716 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2716
                then
                  let uu____2717 =
                    let uu____2718 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2719 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2718 uu____2719 in
                  failwith uu____2717
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___353_2723 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___353_2723.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___353_2723.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2725),uu____2726) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2748 =
                  let uu____2749 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2749 in
                if uu____2748
                then
                  let uu____2750 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2750
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2769;
                FStar_Syntax_Syntax.vars = uu____2770;_},args))
              ->
              ((let uu____2809 =
                  let uu____2810 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2810 Prims.op_Negation in
                if uu____2809
                then
                  let uu____2811 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2811
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2947)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3022) ->
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
                       | ((e2,imp),uu____3059) ->
                           let pat =
                             let uu____3081 = aux argpat e2 in
                             let uu____3082 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3081, uu____3082) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3087 ->
                      let uu____3110 =
                        let uu____3111 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3112 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3111 uu____3112 in
                      failwith uu____3110 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3124;
                     FStar_Syntax_Syntax.vars = uu____3125;_},uu____3126);
                FStar_Syntax_Syntax.pos = uu____3127;
                FStar_Syntax_Syntax.vars = uu____3128;_},args))
              ->
              ((let uu____3171 =
                  let uu____3172 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3172 Prims.op_Negation in
                if uu____3171
                then
                  let uu____3173 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3173
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3309)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3384) ->
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
                       | ((e2,imp),uu____3421) ->
                           let pat =
                             let uu____3443 = aux argpat e2 in
                             let uu____3444 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3443, uu____3444) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3449 ->
                      let uu____3472 =
                        let uu____3473 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3474 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3473 uu____3474 in
                      failwith uu____3472 in
                match_args [] args argpats))
          | uu____3483 ->
              let uu____3488 =
                let uu____3489 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3490 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3491 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3489 uu____3490 uu____3491 in
              failwith uu____3488 in
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
    let pat_as_arg uu____3528 =
      match uu____3528 with
      | (p,i) ->
          let uu____3545 = decorated_pattern_as_term p in
          (match uu____3545 with
           | (vars,te) ->
               let uu____3568 =
                 let uu____3573 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3573) in
               (vars, uu____3568)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3587 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3587)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3591 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3591)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3595 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3595)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3616 =
          let uu____3631 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3631 FStar_List.unzip in
        (match uu____3616 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3741 =
               let uu____3742 =
                 let uu____3743 =
                   let uu____3758 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3758, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3743 in
               mk1 uu____3742 in
             (vars1, uu____3741))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3798)::[] -> wp
      | uu____3815 ->
          let uu____3824 =
            let uu____3825 =
              let uu____3826 =
                FStar_List.map
                  (fun uu____3836  ->
                     match uu____3836 with
                     | (x,uu____3842) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3826 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3825 in
          failwith uu____3824 in
    let uu____3847 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3847, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3861 = destruct_comp c in
        match uu____3861 with
        | (u,uu____3869,wp) ->
            let uu____3871 =
              let uu____3880 =
                let uu____3881 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____3881 in
              [uu____3880] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3871;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3891 =
          let uu____3898 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____3899 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____3898 uu____3899 in
        match uu____3891 with | (m,uu____3901,uu____3902) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3912 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____3912
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
        let uu____3949 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____3949 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____3986 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____3986 with
             | (a,kwp) ->
                 let uu____4017 = destruct_comp m1 in
                 let uu____4024 = destruct_comp m2 in
                 ((md, a, kwp), uu____4017, uu____4024))
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
            let uu____4086 =
              let uu____4087 =
                let uu____4096 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4096] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4087;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4086
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
      let uu___354_4135 = lc in
      let uu____4136 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___354_4135.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4136;
        FStar_Syntax_Syntax.cflags =
          (uu___354_4135.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4141  ->
             let uu____4142 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4142)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4146 =
      let uu____4147 = FStar_Syntax_Subst.compress t in
      uu____4147.FStar_Syntax_Syntax.n in
    match uu____4146 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4150 -> true
    | uu____4163 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4177 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4177
        then c
        else
          (let uu____4179 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4179
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4218 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4218] in
                       let us =
                         let uu____4222 =
                           let uu____4225 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4225] in
                         u_res :: uu____4222 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4229 =
                         let uu____4230 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4231 =
                           let uu____4232 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4233 =
                             let uu____4236 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4237 =
                               let uu____4240 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4240] in
                             uu____4236 :: uu____4237 in
                           uu____4232 :: uu____4233 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4230 uu____4231 in
                       uu____4229 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4244 = destruct_comp c1 in
              match uu____4244 with
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
        let close1 uu____4272 =
          let uu____4273 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4273 in
        let uu___355_4274 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___355_4274.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___355_4274.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___355_4274.FStar_Syntax_Syntax.cflags);
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
          let uu____4285 =
            let uu____4286 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4286 in
          if uu____4285
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let uu____4288 = FStar_Syntax_Util.is_unit t in
             if uu____4288
             then
               FStar_Syntax_Syntax.mk_Total' t
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
             else
               (let m =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Parser_Const.effect_PURE_lid in
                let u_t = env.FStar_TypeChecker_Env.universe_of env t in
                let wp =
                  let uu____4293 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____4293
                  then FStar_Syntax_Syntax.tun
                  else
                    (let uu____4295 =
                       FStar_TypeChecker_Env.wp_signature env
                         FStar_Parser_Const.effect_PURE_lid in
                     match uu____4295 with
                     | (a,kwp) ->
                         let k =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (a, t)] kwp in
                         let uu____4303 =
                           let uu____4304 =
                             let uu____4305 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                             let uu____4306 =
                               let uu____4307 = FStar_Syntax_Syntax.as_arg t in
                               let uu____4308 =
                                 let uu____4311 =
                                   FStar_Syntax_Syntax.as_arg v1 in
                                 [uu____4311] in
                               uu____4307 :: uu____4308 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____4305
                               uu____4306 in
                           uu____4304 FStar_Pervasives_Native.None
                             v1.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.NoFullNorm] env
                           uu____4303) in
                mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
        (let uu____4315 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4315
         then
           let uu____4316 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4317 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4318 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4316
             uu____4317 uu____4318
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
          fun uu____4336  ->
            match uu____4336 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4349 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4349
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4352 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4354 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4355 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4352 uu____4354 bstr uu____4355
                  else ());
                 (let bind_it uu____4360 =
                    let uu____4361 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4361
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4371 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4371
                        then
                          let uu____4372 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4374 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4375 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4376 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4377 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4372 uu____4374 uu____4375 uu____4376
                            uu____4377
                        else ());
                       (let try_simplify uu____4392 =
                          let aux uu____4406 =
                            let uu____4407 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4407
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4436 ->
                                  let uu____4437 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4437
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4464 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4464
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4520 =
                                  let uu____4525 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4525, reason) in
                                FStar_Util.Inl uu____4520
                            | uu____4530 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4549 =
                              let uu____4550 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4550.FStar_Syntax_Syntax.n in
                            match uu____4549 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4554) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4560 -> c in
                          let uu____4561 =
                            let uu____4562 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4562 in
                          if uu____4561
                          then
                            let uu____4575 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4575
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4595 =
                                  let uu____4596 =
                                    let uu____4601 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4601) in
                                  FStar_Errors.Error uu____4596 in
                                FStar_Exn.raise uu____4595))
                          else
                            (let uu____4613 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4613
                             then subst_c2 "both total"
                             else
                               (let uu____4625 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4625
                                then
                                  let uu____4636 =
                                    let uu____4641 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4641, "both gtot") in
                                  FStar_Util.Inl uu____4636
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4667 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4669 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4669) in
                                       if uu____4667
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___356_4682 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___356_4682.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___356_4682.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4683 =
                                           let uu____4688 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4688, "c1 Tot") in
                                         FStar_Util.Inl uu____4683
                                       else aux ()
                                   | uu____4694 -> aux ()))) in
                        let uu____4703 = try_simplify () in
                        match uu____4703 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4727 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4727
                              then
                                let uu____4728 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4729 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4730 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4728 uu____4729 uu____4730
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4739 = lift_and_destruct env c1 c2 in
                            (match uu____4739 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4796 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4796]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4798 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4798] in
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
                                   let uu____4811 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4812 =
                                     let uu____4815 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4816 =
                                       let uu____4819 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4820 =
                                         let uu____4823 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4824 =
                                           let uu____4827 =
                                             let uu____4828 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4828 in
                                           [uu____4827] in
                                         uu____4823 :: uu____4824 in
                                       uu____4819 :: uu____4820 in
                                     uu____4815 :: uu____4816 in
                                   uu____4811 :: uu____4812 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4833 =
                                     let uu____4834 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4834
                                       wp_args in
                                   uu____4833 FStar_Pervasives_Native.None
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
              let uu____4874 =
                let uu____4875 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4875 in
              if uu____4874
              then f
              else (let uu____4877 = reason1 () in label uu____4877 r f)
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
            let uu___357_4888 = g in
            let uu____4889 =
              let uu____4890 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4890 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4889;
              FStar_TypeChecker_Env.deferred =
                (uu___357_4888.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___357_4888.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___357_4888.FStar_TypeChecker_Env.implicits)
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
      | uu____4900 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4919 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4923 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____4923
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____4930 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____4930
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____4935 = destruct_comp c1 in
                    match uu____4935 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____4951 =
                            let uu____4952 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____4953 =
                              let uu____4954 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____4955 =
                                let uu____4958 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____4959 =
                                  let uu____4962 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____4962] in
                                uu____4958 :: uu____4959 in
                              uu____4954 :: uu____4955 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____4952
                              uu____4953 in
                          uu____4951 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___358_4965 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___358_4965.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___358_4965.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___358_4965.FStar_Syntax_Syntax.cflags);
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
            let uu____4998 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____4998
            then (lc, g0)
            else
              ((let uu____5005 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5005
                then
                  let uu____5006 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5007 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5006 uu____5007
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___327_5017  ->
                          match uu___327_5017 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5020 -> [])) in
                let strengthen uu____5026 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5034 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5034 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5041 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5043 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5043) in
                           if uu____5041
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5050 =
                                 let uu____5051 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5051 in
                               FStar_Syntax_Util.comp_set_flags uu____5050
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5057 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5057
                           then
                             let uu____5058 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5059 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5058 uu____5059
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5062 = destruct_comp c2 in
                           match uu____5062 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5078 =
                                   let uu____5079 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5080 =
                                     let uu____5081 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5082 =
                                       let uu____5085 =
                                         let uu____5086 =
                                           let uu____5087 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5087 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5086 in
                                       let uu____5088 =
                                         let uu____5091 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5091] in
                                       uu____5085 :: uu____5088 in
                                     uu____5081 :: uu____5082 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5079
                                     uu____5080 in
                                 uu____5078 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5095 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5095
                                 then
                                   let uu____5096 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5096
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5099 =
                  let uu___359_5100 = lc in
                  let uu____5101 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5102 =
                    let uu____5105 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5107 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5107) in
                    if uu____5105 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5101;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___359_5100.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5102;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5099,
                  (let uu___360_5112 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___360_5112.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___360_5112.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___360_5112.FStar_TypeChecker_Env.implicits)
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
        let uu____5127 =
          let uu____5132 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5133 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5132, uu____5133) in
        match uu____5127 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5142 =
                let uu____5143 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5144 =
                  let uu____5145 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5146 =
                    let uu____5149 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5149] in
                  uu____5145 :: uu____5146 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5143 uu____5144 in
              uu____5142 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5155 =
                let uu____5156 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5157 =
                  let uu____5158 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5159 =
                    let uu____5162 =
                      let uu____5163 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5163 in
                    let uu____5164 =
                      let uu____5167 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5167] in
                    uu____5162 :: uu____5164 in
                  uu____5158 :: uu____5159 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5156 uu____5157 in
              uu____5155 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5173 =
                let uu____5174 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5175 =
                  let uu____5176 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5177 =
                    let uu____5180 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5181 =
                      let uu____5184 =
                        let uu____5185 =
                          let uu____5186 =
                            let uu____5187 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5187] in
                          FStar_Syntax_Util.abs uu____5186 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5185 in
                      [uu____5184] in
                    uu____5180 :: uu____5181 in
                  uu____5176 :: uu____5177 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5174 uu____5175 in
              uu____5173 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5194 = FStar_TypeChecker_Env.get_range env in
              bind uu____5194 env FStar_Pervasives_Native.None
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
          let comp uu____5213 =
            let uu____5214 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5214
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5217 =
                 let uu____5242 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5243 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5242 uu____5243 in
               match uu____5217 with
               | ((md,uu____5245,uu____5246),(u_res_t,res_t,wp_then),
                  (uu____5250,uu____5251,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5289 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5290 =
                       let uu____5291 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5292 =
                         let uu____5293 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5294 =
                           let uu____5297 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5298 =
                             let uu____5301 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5302 =
                               let uu____5305 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5305] in
                             uu____5301 :: uu____5302 in
                           uu____5297 :: uu____5298 in
                         uu____5293 :: uu____5294 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5291 uu____5292 in
                     uu____5290 FStar_Pervasives_Native.None uu____5289 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5311 =
                     let uu____5312 = FStar_Options.split_cases () in
                     uu____5312 > (Prims.parse_int "0") in
                   if uu____5311
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5318 =
                          let uu____5319 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5320 =
                            let uu____5321 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5322 =
                              let uu____5325 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5325] in
                            uu____5321 :: uu____5322 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5319 uu____5320 in
                        uu____5318 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5328 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5328;
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
      let uu____5335 =
        let uu____5336 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5336 in
      FStar_Syntax_Syntax.fvar uu____5335 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5368  ->
                 match uu____5368 with
                 | (uu____5373,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5378 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5380 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5380
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5400 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5401 =
                 let uu____5402 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5403 =
                   let uu____5404 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5405 =
                     let uu____5408 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5409 =
                       let uu____5412 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5413 =
                         let uu____5416 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5416] in
                       uu____5412 :: uu____5413 in
                     uu____5408 :: uu____5409 in
                   uu____5404 :: uu____5405 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5402 uu____5403 in
               uu____5401 FStar_Pervasives_Native.None uu____5400 in
             let default_case =
               let post_k =
                 let uu____5423 =
                   let uu____5430 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5430] in
                 let uu____5431 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5423 uu____5431 in
               let kwp =
                 let uu____5437 =
                   let uu____5444 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5444] in
                 let uu____5445 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5437 uu____5445 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5450 =
                   let uu____5451 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5451] in
                 let uu____5452 =
                   let uu____5453 =
                     let uu____5456 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5456 in
                   let uu____5457 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5453 uu____5457 in
                 FStar_Syntax_Util.abs uu____5450 uu____5452
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
                 (fun uu____5481  ->
                    fun celse  ->
                      match uu____5481 with
                      | (g,cthen) ->
                          let uu____5489 =
                            let uu____5514 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5514 celse in
                          (match uu____5489 with
                           | ((md,uu____5516,uu____5517),(uu____5518,uu____5519,wp_then),
                              (uu____5521,uu____5522,wp_else)) ->
                               let uu____5542 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5542 []))
                 lcases default_case in
             let uu____5543 =
               let uu____5544 = FStar_Options.split_cases () in
               uu____5544 > (Prims.parse_int "0") in
             if uu____5543
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5548 = destruct_comp comp1 in
                match uu____5548 with
                | (uu____5555,uu____5556,wp) ->
                    let wp1 =
                      let uu____5561 =
                        let uu____5562 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5563 =
                          let uu____5564 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5565 =
                            let uu____5568 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5568] in
                          uu____5564 :: uu____5565 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5562 uu____5563 in
                      uu____5561 FStar_Pervasives_Native.None
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
          let uu____5583 =
            ((let uu____5586 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5586) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5588 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5588) in
          if uu____5583
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5597 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5601 =
            ((let uu____5604 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5604) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5601
          then c
          else
            (let uu____5608 = FStar_Syntax_Util.is_partial_return c in
             if uu____5608
             then c
             else
               (let uu____5612 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5612
                then
                  let uu____5615 =
                    let uu____5616 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5616 in
                  (if uu____5615
                   then
                     let uu____5619 =
                       let uu____5620 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5621 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5620 uu____5621 in
                     failwith uu____5619
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5626 =
                        let uu____5627 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5627 in
                      if uu____5626
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___361_5632 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___361_5632.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___361_5632.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___361_5632.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5643 =
                       let uu____5646 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5646
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5643 in
                   let eq1 =
                     let uu____5650 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5650 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5652 =
                     let uu____5653 =
                       let uu____5658 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5658.FStar_Syntax_Syntax.comp in
                     uu____5653 () in
                   FStar_Syntax_Util.comp_set_flags uu____5652 flags))) in
        let uu____5661 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____5661
        then lc
        else
          (let uu___362_5663 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___362_5663.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___362_5663.FStar_Syntax_Syntax.res_typ);
             FStar_Syntax_Syntax.cflags = flags;
             FStar_Syntax_Syntax.comp = refine1
           })
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
          let uu____5688 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5688 with
          | FStar_Pervasives_Native.None  ->
              let uu____5697 =
                let uu____5698 =
                  let uu____5703 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5704 = FStar_TypeChecker_Env.get_range env in
                  (uu____5703, uu____5704) in
                FStar_Errors.Error uu____5698 in
              FStar_Exn.raise uu____5697
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
            let uu____5737 =
              let uu____5738 = FStar_Syntax_Subst.compress t2 in
              uu____5738.FStar_Syntax_Syntax.n in
            match uu____5737 with
            | FStar_Syntax_Syntax.Tm_type uu____5741 -> true
            | uu____5742 -> false in
          let uu____5743 =
            let uu____5744 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5744.FStar_Syntax_Syntax.n in
          match uu____5743 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5752 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5763 =
                  let uu____5764 =
                    let uu____5765 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5765 in
                  (FStar_Pervasives_Native.None, uu____5764) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5763 in
              let e1 =
                let uu____5775 =
                  let uu____5776 =
                    let uu____5777 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5777] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5776 in
                uu____5775 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5782 -> (e, lc)
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
              (let uu____5811 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5811 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5834 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5856 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5856, false)
            else
              (let uu____5862 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5862, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____5873) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____5882 =
                  let uu____5883 =
                    let uu____5888 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____5888, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____5883 in
                FStar_Exn.raise uu____5882
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___363_5898 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___363_5898.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___363_5898.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___363_5898.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____5903 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____5903 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___364_5911 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___364_5911.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___364_5911.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___364_5911.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___365_5914 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___365_5914.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___365_5914.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___365_5914.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____5920 =
                     let uu____5921 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____5921
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____5926 =
                          let uu____5927 = FStar_Syntax_Subst.compress f1 in
                          uu____5927.FStar_Syntax_Syntax.n in
                        match uu____5926 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____5932,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____5934;
                                          FStar_Syntax_Syntax.vars =
                                            uu____5935;_},uu____5936)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___366_5958 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___366_5958.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___366_5958.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___366_5958.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____5959 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____5964 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____5964
                              then
                                let uu____5965 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____5966 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____5967 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____5968 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____5965 uu____5966 uu____5967 uu____5968
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____5971 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____5971 with
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
                                  let uu____5984 = destruct_comp ct in
                                  (match uu____5984 with
                                   | (u_t,uu____5994,uu____5995) ->
                                       let wp =
                                         let uu____5999 =
                                           let uu____6000 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6001 =
                                             let uu____6002 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6003 =
                                               let uu____6006 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6006] in
                                             uu____6002 :: uu____6003 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6000 uu____6001 in
                                         uu____5999
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6010 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6010 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6020 =
                                             let uu____6021 =
                                               let uu____6022 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6022] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6021 in
                                           uu____6020
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6026 =
                                         let uu____6031 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6044 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6045 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6031
                                           uu____6044 e cret uu____6045 in
                                       (match uu____6026 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___367_6051 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___367_6051.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___367_6051.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6053 =
                                                let uu____6054 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6054 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6053
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6065 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6065
                                              then
                                                let uu____6066 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6066
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___328_6076  ->
                             match uu___328_6076 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6079 -> [])) in
                   let lc1 =
                     let uu___368_6081 = lc in
                     let uu____6082 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6082;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___369_6084 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___369_6084.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___369_6084.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___369_6084.FStar_TypeChecker_Env.implicits)
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
        let uu____6107 =
          let uu____6108 =
            let uu____6109 =
              let uu____6110 =
                let uu____6111 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6111 in
              [uu____6110] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6109 in
          uu____6108 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6107 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6118 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6118
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6136 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6151 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6180)::(ens,uu____6182)::uu____6183 ->
                    let uu____6212 =
                      let uu____6215 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6215 in
                    let uu____6216 =
                      let uu____6217 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6217 in
                    (uu____6212, uu____6216)
                | uu____6220 ->
                    let uu____6229 =
                      let uu____6230 =
                        let uu____6235 =
                          let uu____6236 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6236 in
                        (uu____6235, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6230 in
                    FStar_Exn.raise uu____6229)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6252)::uu____6253 ->
                    let uu____6272 =
                      let uu____6277 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6277 in
                    (match uu____6272 with
                     | (us_r,uu____6309) ->
                         let uu____6310 =
                           let uu____6315 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6315 in
                         (match uu____6310 with
                          | (us_e,uu____6347) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6350 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6350
                                  us_r in
                              let as_ens =
                                let uu____6352 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6352
                                  us_e in
                              let req =
                                let uu____6356 =
                                  let uu____6357 =
                                    let uu____6358 =
                                      let uu____6369 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6369] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6358 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6357 in
                                uu____6356 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6387 =
                                  let uu____6388 =
                                    let uu____6389 =
                                      let uu____6400 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6400] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6389 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6388 in
                                uu____6387 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6415 =
                                let uu____6418 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6418 in
                              let uu____6419 =
                                let uu____6420 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6420 in
                              (uu____6415, uu____6419)))
                | uu____6423 -> failwith "Impossible"))
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
      (let uu____6449 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6449
       then
         let uu____6450 = FStar_Syntax_Print.term_to_string tm in
         let uu____6451 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6450 uu____6451
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
        (let uu____6469 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6469
         then
           let uu____6470 = FStar_Syntax_Print.term_to_string tm in
           let uu____6471 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6470
             uu____6471
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6476 =
      let uu____6477 =
        let uu____6478 = FStar_Syntax_Subst.compress t in
        uu____6478.FStar_Syntax_Syntax.n in
      match uu____6477 with
      | FStar_Syntax_Syntax.Tm_app uu____6481 -> false
      | uu____6496 -> true in
    if uu____6476
    then t
    else
      (let uu____6498 = FStar_Syntax_Util.head_and_args t in
       match uu____6498 with
       | (head1,args) ->
           let uu____6535 =
             let uu____6536 =
               let uu____6537 = FStar_Syntax_Subst.compress head1 in
               uu____6537.FStar_Syntax_Syntax.n in
             match uu____6536 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6540 -> false in
           if uu____6535
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6562 ->
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
             let uu____6599 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6599 with
             | (formals,uu____6613) ->
                 let n_implicits =
                   let uu____6631 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6707  ->
                             match uu____6707 with
                             | (uu____6714,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6631 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6845 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6845 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____6869 =
                     let uu____6870 =
                       let uu____6875 =
                         let uu____6876 = FStar_Util.string_of_int n_expected in
                         let uu____6883 = FStar_Syntax_Print.term_to_string e in
                         let uu____6884 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____6876 uu____6883 uu____6884 in
                       let uu____6891 = FStar_TypeChecker_Env.get_range env in
                       (uu____6875, uu____6891) in
                     FStar_Errors.Error uu____6870 in
                   FStar_Exn.raise uu____6869
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___329_6912 =
             match uu___329_6912 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____6942 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____6942 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7051) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7094,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7127 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7127 with
                           | (v1,uu____7167,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7184 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7184 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7277 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7277)))
                      | (uu____7304,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7350 =
                      let uu____7377 = inst_n_binders t in
                      aux [] uu____7377 bs1 in
                    (match uu____7350 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7448) -> (e, torig, guard)
                          | (uu____7479,[]) when
                              let uu____7510 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7510 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7511 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7543 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7558 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7566 =
      let uu____7569 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7569
        (FStar_List.map
           (fun u  ->
              let uu____7579 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7579 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7566 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7596 = FStar_Util.set_is_empty x in
      if uu____7596
      then []
      else
        (let s =
           let uu____7603 =
             let uu____7606 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7606 in
           FStar_All.pipe_right uu____7603 FStar_Util.set_elements in
         (let uu____7614 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7614
          then
            let uu____7615 =
              let uu____7616 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7616 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7615
          else ());
         (let r =
            let uu____7623 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7623 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7638 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7638
                     then
                       let uu____7639 =
                         let uu____7640 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7640 in
                       let uu____7641 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7642 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7639 uu____7641 uu____7642
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
        let uu____7664 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7664 FStar_Util.fifo_set_elements in
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
        | ([],uu____7696) -> generalized_univ_names
        | (uu____7703,[]) -> explicit_univ_names
        | uu____7710 ->
            let uu____7719 =
              let uu____7720 =
                let uu____7725 =
                  let uu____7726 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7726 in
                (uu____7725, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7720 in
            FStar_Exn.raise uu____7719
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
      (let uu____7743 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7743
       then
         let uu____7744 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7744
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7750 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7750
        then
          let uu____7751 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7751
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
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____7821 =
          let uu____7822 =
            FStar_Util.for_all
              (fun uu____7835  ->
                 match uu____7835 with
                 | (uu____7844,uu____7845,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7822 in
        if uu____7821
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7891 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____7891
              then
                let uu____7892 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7892
              else ());
             (let c1 =
                let uu____7895 = FStar_TypeChecker_Env.should_verify env in
                if uu____7895
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
              (let uu____7898 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____7898
               then
                 let uu____7899 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7899
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____7960 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____7960 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8090 =
             match uu____8090 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8156 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8156
                   then
                     let uu____8157 =
                       let uu____8158 =
                         let uu____8161 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8161
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8158
                         (FStar_String.concat ", ") in
                     let uu____8188 =
                       let uu____8189 =
                         let uu____8192 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8192
                           (FStar_List.map
                              (fun uu____8220  ->
                                 match uu____8220 with
                                 | (u,t2) ->
                                     let uu____8227 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8228 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8227 uu____8228)) in
                       FStar_All.pipe_right uu____8189
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8157
                       uu____8188
                   else ());
                  (let univs2 =
                     let uu____8235 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8258  ->
                            match uu____8258 with
                            | (uu____8267,t2) ->
                                let uu____8269 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8269)
                       univs1 uu____8235 in
                   let uvs = gen_uvars uvt in
                   (let uu____8292 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8292
                    then
                      let uu____8293 =
                        let uu____8294 =
                          let uu____8297 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8297
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8294
                          (FStar_String.concat ", ") in
                      let uu____8324 =
                        let uu____8325 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8357  ->
                                  match uu____8357 with
                                  | (u,t2) ->
                                      let uu____8364 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8365 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8364 uu____8365)) in
                        FStar_All.pipe_right uu____8325
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8293
                        uu____8324
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8395 =
             let uu____8428 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8428 in
           match uu____8395 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8546 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8546
                 then ()
                 else
                   (let uu____8548 = lec_hd in
                    match uu____8548 with
                    | (lb1,uu____8556,uu____8557) ->
                        let uu____8558 = lec2 in
                        (match uu____8558 with
                         | (lb2,uu____8566,uu____8567) ->
                             let msg =
                               let uu____8569 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8570 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8569 uu____8570 in
                             let uu____8571 =
                               let uu____8572 =
                                 let uu____8577 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8577) in
                               FStar_Errors.Error uu____8572 in
                             FStar_Exn.raise uu____8571)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8688  ->
                           match uu____8688 with
                           | (u,uu____8696) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8718  ->
                                       match uu____8718 with
                                       | (u',uu____8726) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8731 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8731
                 then ()
                 else
                   (let uu____8733 = lec_hd in
                    match uu____8733 with
                    | (lb1,uu____8741,uu____8742) ->
                        let uu____8743 = lec2 in
                        (match uu____8743 with
                         | (lb2,uu____8751,uu____8752) ->
                             let msg =
                               let uu____8754 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8755 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8754 uu____8755 in
                             let uu____8756 =
                               let uu____8757 =
                                 let uu____8762 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8762) in
                               FStar_Errors.Error uu____8757 in
                             FStar_Exn.raise uu____8756)) in
               let lecs1 =
                 let uu____8772 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8831 = univs_and_uvars_of_lec this_lec in
                        match uu____8831 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8772 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____8984 = lec_hd in
                   match uu____8984 with
                   | (lbname,e,c) ->
                       let uu____8994 =
                         let uu____8995 =
                           let uu____9000 =
                             let uu____9001 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9002 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9003 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9001 uu____9002 uu____9003 in
                           let uu____9004 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9000, uu____9004) in
                         FStar_Errors.Error uu____8995 in
                       FStar_Exn.raise uu____8994 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9034  ->
                         match uu____9034 with
                         | (u,k) ->
                             let uu____9047 = FStar_Syntax_Unionfind.find u in
                             (match uu____9047 with
                              | FStar_Pervasives_Native.Some uu____9056 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9063 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9067 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9067 with
                                   | (bs,kres) ->
                                       ((let uu____9105 =
                                           let uu____9106 =
                                             let uu____9109 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9109 in
                                           uu____9106.FStar_Syntax_Syntax.n in
                                         match uu____9105 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9110 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9114 =
                                               let uu____9115 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9115 in
                                             if uu____9114
                                             then fail kres
                                             else ()
                                         | uu____9117 -> fail kres);
                                        (let a =
                                           let uu____9119 =
                                             let uu____9122 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9122 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9119 kres in
                                         let t =
                                           let uu____9126 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9126
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.residual_tot
                                                   kres)) in
                                         FStar_Syntax_Util.set_uvar u t;
                                         (a,
                                           (FStar_Pervasives_Native.Some
                                              FStar_Syntax_Syntax.imp_tag)))))))) in
               let gen_univs1 = gen_univs env univs1 in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9245  ->
                         match uu____9245 with
                         | (lbname,e,c) ->
                             let uu____9291 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9360 ->
                                   let uu____9375 = (e, c) in
                                   (match uu____9375 with
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
                                                (fun uu____9412  ->
                                                   match uu____9412 with
                                                   | (x,uu____9420) ->
                                                       let uu____9425 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9425)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9435 =
                                                let uu____9436 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9436 in
                                              if uu____9435
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
                                          let uu____9444 =
                                            let uu____9445 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9445.FStar_Syntax_Syntax.n in
                                          match uu____9444 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9468 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9468 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9483 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9485 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9485, gen_tvars)) in
                             (match uu____9291 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs)))) in
               FStar_Pervasives_Native.Some ecs)
let generalize:
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____9631 = Obj.magic () in ());
        (let uu____9633 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9633
         then
           let uu____9634 =
             let uu____9635 =
               FStar_List.map
                 (fun uu____9648  ->
                    match uu____9648 with
                    | (lb,uu____9656,uu____9657) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9635 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9634
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9678  ->
                match uu____9678 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9707 = gen env is_rec lecs in
           match uu____9707 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9806  ->
                       match uu____9806 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9868 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____9868
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9912  ->
                           match uu____9912 with
                           | (l,us,e,c,gvs) ->
                               let uu____9946 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____9947 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____9948 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____9949 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____9950 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9946 uu____9947 uu____9948 uu____9949
                                 uu____9950))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9991  ->
                match uu____9991 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10035 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10035, t, c, gvs)) univnames_lecs
           generalized_lecs)
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
              (let uu____10078 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____10078 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10084 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10084) in
          let is_var e1 =
            let uu____10091 =
              let uu____10092 = FStar_Syntax_Subst.compress e1 in
              uu____10092.FStar_Syntax_Syntax.n in
            match uu____10091 with
            | FStar_Syntax_Syntax.Tm_name uu____10095 -> true
            | uu____10096 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___370_10112 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___370_10112.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___370_10112.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10113 -> e2 in
          let env2 =
            let uu___371_10115 = env1 in
            let uu____10116 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___371_10115.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___371_10115.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___371_10115.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___371_10115.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___371_10115.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___371_10115.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___371_10115.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___371_10115.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___371_10115.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___371_10115.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___371_10115.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___371_10115.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___371_10115.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___371_10115.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___371_10115.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10116;
              FStar_TypeChecker_Env.is_iface =
                (uu___371_10115.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___371_10115.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___371_10115.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___371_10115.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___371_10115.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___371_10115.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___371_10115.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___371_10115.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___371_10115.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___371_10115.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___371_10115.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___371_10115.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___371_10115.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___371_10115.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___371_10115.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___371_10115.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___371_10115.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___371_10115.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10117 = check env2 t1 t2 in
          match uu____10117 with
          | FStar_Pervasives_Native.None  ->
              let uu____10124 =
                let uu____10125 =
                  let uu____10130 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10131 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10130, uu____10131) in
                FStar_Errors.Error uu____10125 in
              FStar_Exn.raise uu____10124
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10138 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10138
                then
                  let uu____10139 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10139
                else ());
               (let uu____10141 = decorate e t2 in (uu____10141, g)))
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
        let uu____10169 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10169
        then
          let uu____10174 = discharge g1 in
          let uu____10175 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10174, uu____10175)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10188 =
               let uu____10189 =
                 let uu____10190 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10190 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10189
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10188
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10192 = destruct_comp c1 in
           match uu____10192 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10209 = FStar_TypeChecker_Env.get_range env in
                 let uu____10210 =
                   let uu____10211 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10212 =
                     let uu____10213 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10214 =
                       let uu____10217 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10217] in
                     uu____10213 :: uu____10214 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10211 uu____10212 in
                 uu____10210 FStar_Pervasives_Native.None uu____10209 in
               ((let uu____10221 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10221
                 then
                   let uu____10222 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10222
                 else ());
                (let g2 =
                   let uu____10225 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10225 in
                 let uu____10226 = discharge g2 in
                 let uu____10227 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10226, uu____10227))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___330_10251 =
        match uu___330_10251 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10259)::[] -> f fst1
        | uu____10276 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10281 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10281
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10290 =
          let uu____10293 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10293 in
        FStar_All.pipe_right uu____10290
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10304 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10304
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___331_10318 =
        match uu___331_10318 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10326)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10345)::[] ->
            let uu____10374 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10374
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10379 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10389 =
          let uu____10396 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10396) in
        let uu____10401 =
          let uu____10410 =
            let uu____10417 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10417) in
          let uu____10422 =
            let uu____10431 =
              let uu____10438 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10438) in
            let uu____10443 =
              let uu____10452 =
                let uu____10459 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10459) in
              let uu____10464 =
                let uu____10473 =
                  let uu____10480 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10480) in
                [uu____10473; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10452 :: uu____10464 in
            uu____10431 :: uu____10443 in
          uu____10410 :: uu____10422 in
        uu____10389 :: uu____10401 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10531 =
            FStar_Util.find_map table
              (fun uu____10544  ->
                 match uu____10544 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10561 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10561
                     else FStar_Pervasives_Native.None) in
          (match uu____10531 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10564 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10568 =
      let uu____10569 = FStar_Syntax_Util.un_uinst l in
      uu____10569.FStar_Syntax_Syntax.n in
    match uu____10568 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10573 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10597)::uu____10598 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10609 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10616,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10617))::uu____10618 -> bs
      | uu____10635 ->
          let uu____10636 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10636 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10640 =
                 let uu____10641 = FStar_Syntax_Subst.compress t in
                 uu____10641.FStar_Syntax_Syntax.n in
               (match uu____10640 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10645) ->
                    let uu____10662 =
                      FStar_Util.prefix_until
                        (fun uu___332_10702  ->
                           match uu___332_10702 with
                           | (uu____10709,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10710)) ->
                               false
                           | uu____10713 -> true) bs' in
                    (match uu____10662 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10748,uu____10749) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10821,uu____10822) ->
                         let uu____10895 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10913  ->
                                   match uu____10913 with
                                   | (x,uu____10921) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10895
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10968  ->
                                     match uu____10968 with
                                     | (x,i) ->
                                         let uu____10987 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10987, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10997 -> bs))
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
          let uu____11029 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11029
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
        (let uu____11052 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11052
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11054 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11054))
         else ());
        (let fv =
           let uu____11057 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11057
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
         let uu____11065 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___372_11071 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___372_11071.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___372_11071.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___372_11071.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___372_11071.FStar_Syntax_Syntax.sigattrs)
           }), uu____11065))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___333_11081 =
        match uu___333_11081 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11082 -> false in
      let reducibility uu___334_11086 =
        match uu___334_11086 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11087 -> false in
      let assumption uu___335_11091 =
        match uu___335_11091 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11092 -> false in
      let reification uu___336_11096 =
        match uu___336_11096 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11097 -> true
        | uu____11098 -> false in
      let inferred uu___337_11102 =
        match uu___337_11102 with
        | FStar_Syntax_Syntax.Discriminator uu____11103 -> true
        | FStar_Syntax_Syntax.Projector uu____11104 -> true
        | FStar_Syntax_Syntax.RecordType uu____11109 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11118 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11127 -> false in
      let has_eq uu___338_11131 =
        match uu___338_11131 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11132 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11192 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11197 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11201 =
        let uu____11202 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___339_11206  ->
                  match uu___339_11206 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11207 -> false)) in
        FStar_All.pipe_right uu____11202 Prims.op_Negation in
      if uu____11201
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11220 =
            let uu____11221 =
              let uu____11226 =
                let uu____11227 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11227 msg in
              (uu____11226, r) in
            FStar_Errors.Error uu____11221 in
          FStar_Exn.raise uu____11220 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11235 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11239 =
            let uu____11240 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11240 in
          if uu____11239 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11245),uu____11246) ->
              ((let uu____11262 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11262
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11266 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11266
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11272 ->
              let uu____11281 =
                let uu____11282 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11282 in
              if uu____11281 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11288 ->
              let uu____11295 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11295 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11299 ->
              let uu____11306 =
                let uu____11307 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11307 in
              if uu____11306 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11313 ->
              let uu____11314 =
                let uu____11315 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11315 in
              if uu____11314 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11321 ->
              let uu____11322 =
                let uu____11323 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11323 in
              if uu____11322 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11329 ->
              let uu____11342 =
                let uu____11343 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11343 in
              if uu____11342 then err'1 () else ()
          | uu____11349 -> ()))
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
                          let uu____11412 =
                            let uu____11415 =
                              let uu____11416 =
                                let uu____11423 =
                                  let uu____11424 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11424 in
                                (uu____11423, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11416 in
                            FStar_Syntax_Syntax.mk uu____11415 in
                          uu____11412 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11465  ->
                                  match uu____11465 with
                                  | (x,imp) ->
                                      let uu____11476 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11476, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11478 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11478 in
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
                             let uu____11487 =
                               let uu____11488 =
                                 let uu____11489 =
                                   let uu____11490 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11491 =
                                     let uu____11492 =
                                       let uu____11493 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11493 in
                                     [uu____11492] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11490
                                     uu____11491 in
                                 uu____11489 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11488 in
                             FStar_Syntax_Util.refine x uu____11487 in
                           let uu____11496 =
                             let uu___373_11497 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___373_11497.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___373_11497.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11496) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11512 =
                          FStar_List.map
                            (fun uu____11534  ->
                               match uu____11534 with
                               | (x,uu____11546) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11512 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11595  ->
                                match uu____11595 with
                                | (x,uu____11607) ->
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
                             (let uu____11621 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11621)
                               ||
                               (let uu____11623 =
                                  let uu____11624 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11624.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11623) in
                           let quals =
                             let uu____11628 =
                               let uu____11631 =
                                 let uu____11634 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11634
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11638 =
                                 FStar_List.filter
                                   (fun uu___340_11642  ->
                                      match uu___340_11642 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11643 -> false) iquals in
                               FStar_List.append uu____11631 uu____11638 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11628 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11664 =
                                 let uu____11665 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11665 in
                               FStar_Syntax_Syntax.mk_Total uu____11664 in
                             let uu____11666 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11666 in
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
                           (let uu____11669 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11669
                            then
                              let uu____11670 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11670
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
                                             fun uu____11723  ->
                                               match uu____11723 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11747 =
                                                       let uu____11750 =
                                                         let uu____11751 =
                                                           let uu____11758 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11758,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11751 in
                                                       pos uu____11750 in
                                                     (uu____11747, b)
                                                   else
                                                     (let uu____11762 =
                                                        let uu____11765 =
                                                          let uu____11766 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11766 in
                                                        pos uu____11765 in
                                                      (uu____11762, b)))) in
                                   let pat_true =
                                     let uu____11784 =
                                       let uu____11787 =
                                         let uu____11788 =
                                           let uu____11801 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11801, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11788 in
                                       pos uu____11787 in
                                     (uu____11784,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____11835 =
                                       let uu____11838 =
                                         let uu____11839 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____11839 in
                                       pos uu____11838 in
                                     (uu____11835,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____11851 =
                                     let uu____11854 =
                                       let uu____11855 =
                                         let uu____11878 =
                                           let uu____11881 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____11882 =
                                             let uu____11885 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____11885] in
                                           uu____11881 :: uu____11882 in
                                         (arg_exp, uu____11878) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11855 in
                                     FStar_Syntax_Syntax.mk uu____11854 in
                                   uu____11851 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____11892 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____11892
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
                                let uu____11900 =
                                  let uu____11905 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____11905 in
                                let uu____11906 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____11900;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____11906
                                } in
                              let impl =
                                let uu____11910 =
                                  let uu____11911 =
                                    let uu____11918 =
                                      let uu____11921 =
                                        let uu____11922 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____11922
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____11921] in
                                    ((false, [lb]), uu____11918) in
                                  FStar_Syntax_Syntax.Sig_let uu____11911 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____11910;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____11940 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____11940
                               then
                                 let uu____11941 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____11941
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
                                fun uu____11983  ->
                                  match uu____11983 with
                                  | (a,uu____11989) ->
                                      let uu____11990 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____11990 with
                                       | (field_name,uu____11996) ->
                                           let field_proj_tm =
                                             let uu____11998 =
                                               let uu____11999 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____11999 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____11998 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12016 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12048  ->
                                    match uu____12048 with
                                    | (x,uu____12056) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12058 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12058 with
                                         | (field_name,uu____12066) ->
                                             let t =
                                               let uu____12068 =
                                                 let uu____12069 =
                                                   let uu____12072 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12072 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12069 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12068 in
                                             let only_decl =
                                               (let uu____12076 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12076)
                                                 ||
                                                 (let uu____12078 =
                                                    let uu____12079 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12079.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12078) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12093 =
                                                   FStar_List.filter
                                                     (fun uu___341_12097  ->
                                                        match uu___341_12097
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12098 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12093
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___342_12111  ->
                                                         match uu___342_12111
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12112 ->
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
                                             ((let uu____12131 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12131
                                               then
                                                 let uu____12132 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12132
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
                                                           fun uu____12180 
                                                             ->
                                                             match uu____12180
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12204
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12204,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12220
                                                                    =
                                                                    let uu____12223
                                                                    =
                                                                    let uu____12224
                                                                    =
                                                                    let uu____12231
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12231,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12224 in
                                                                    pos
                                                                    uu____12223 in
                                                                    (uu____12220,
                                                                    b))
                                                                   else
                                                                    (let uu____12235
                                                                    =
                                                                    let uu____12238
                                                                    =
                                                                    let uu____12239
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12239 in
                                                                    pos
                                                                    uu____12238 in
                                                                    (uu____12235,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12255 =
                                                     let uu____12258 =
                                                       let uu____12259 =
                                                         let uu____12272 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12272,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12259 in
                                                     pos uu____12258 in
                                                   let uu____12281 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12255,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12281) in
                                                 let body =
                                                   let uu____12293 =
                                                     let uu____12296 =
                                                       let uu____12297 =
                                                         let uu____12320 =
                                                           let uu____12323 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12323] in
                                                         (arg_exp,
                                                           uu____12320) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12297 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12296 in
                                                   uu____12293
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12331 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12331
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
                                                   let uu____12338 =
                                                     let uu____12343 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12343 in
                                                   let uu____12344 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12338;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12344
                                                   } in
                                                 let impl =
                                                   let uu____12348 =
                                                     let uu____12349 =
                                                       let uu____12356 =
                                                         let uu____12359 =
                                                           let uu____12360 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12360
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12359] in
                                                       ((false, [lb]),
                                                         uu____12356) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12349 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12348;
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
                                                 (let uu____12378 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12378
                                                  then
                                                    let uu____12379 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12379
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12016 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12419) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12424 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12424 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12446 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12446 with
                    | (formals,uu____12462) ->
                        let uu____12479 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12511 =
                                   let uu____12512 =
                                     let uu____12513 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12513 in
                                   FStar_Ident.lid_equals typ_lid uu____12512 in
                                 if uu____12511
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12532,uvs',tps,typ0,uu____12536,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12555 -> failwith "Impossible"
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
                        (match uu____12479 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12628 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12628 with
                              | (indices,uu____12644) ->
                                  let refine_domain =
                                    let uu____12662 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___343_12667  ->
                                              match uu___343_12667 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12668 -> true
                                              | uu____12677 -> false)) in
                                    if uu____12662
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___344_12685 =
                                      match uu___344_12685 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12688,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12700 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12701 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12701 with
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
                                    let uu____12712 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12712 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12777  ->
                                               fun uu____12778  ->
                                                 match (uu____12777,
                                                         uu____12778)
                                                 with
                                                 | ((x,uu____12796),(x',uu____12798))
                                                     ->
                                                     let uu____12807 =
                                                       let uu____12814 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12814) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12807) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12815 -> []