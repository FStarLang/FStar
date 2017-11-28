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
  fun uu___266_89  ->
    match uu___266_89 with
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
                     let uu___285_253 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____254 =
                       let uu____269 =
                         let uu____282 = as_uvar u in
                         (reason, env, uu____282, t, k, r) in
                       [uu____269] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___285_253.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___285_253.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___285_253.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___286_488 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___286_488.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___286_488.FStar_Syntax_Syntax.index);
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
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____1084 =
              let uu____1089 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
              match uu____1089 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1094;
                  FStar_Syntax_Syntax.vars = uu____1095;_} ->
                  let uu____1098 = FStar_Syntax_Util.type_u () in
                  (match uu____1098 with
                   | (t,uu____1108) ->
                       let uu____1109 = new_uvar env1 t in
                       (uu____1109, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t in
            match uu____1084 with
            | (t_x,guard) ->
                ((let uu___287_1118 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___287_1118.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___287_1118.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard) in
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
                  | uu____1187 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1195) ->
                let uu____1200 = FStar_Syntax_Util.type_u () in
                (match uu____1200 with
                 | (k,uu____1226) ->
                     let t = new_uvar env1 k in
                     let x1 =
                       let uu___288_1229 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___288_1229.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___288_1229.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       } in
                     let uu____1230 =
                       let uu____1235 =
                         FStar_TypeChecker_Env.all_binders env1 in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1235 t in
                     (match uu____1230 with
                      | (e,u) ->
                          let p2 =
                            let uu___289_1261 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___289_1261.FStar_Syntax_Syntax.p)
                            } in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1271 = check_bv env1 x in
                (match uu____1271 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1 in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1312 = check_bv env1 x in
                (match uu____1312 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1369 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1505  ->
                          fun uu____1506  ->
                            match (uu____1505, uu____1506) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1704 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2 in
                                (match uu____1704 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     let uu____1780 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard' in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1780, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, [])) in
                (match uu____1369 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1911 =
                         let uu____1914 =
                           let uu____1915 =
                             let uu____1922 =
                               let uu____1925 =
                                 let uu____1926 =
                                   FStar_Syntax_Syntax.fv_to_tm fv in
                                 let uu____1927 =
                                   FStar_All.pipe_right args FStar_List.rev in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1926
                                   uu____1927 in
                               uu____1925 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p in
                             (uu____1922,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app)) in
                           FStar_Syntax_Syntax.Tm_meta uu____1915 in
                         FStar_Syntax_Syntax.mk uu____1914 in
                       uu____1911 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     let uu____1939 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu____1950 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu____1961 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu____1939, uu____1950, uu____1961, env2, e, guard,
                       (let uu___290_1983 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___290_1983.FStar_Syntax_Syntax.p)
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
                    (fun uu____2067  ->
                       match uu____2067 with
                       | (p2,imp) ->
                           let uu____2086 = elaborate_pat env1 p2 in
                           (uu____2086, imp)) pats in
                let uu____2091 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2091 with
                 | (uu____2098,t) ->
                     let uu____2100 = FStar_Syntax_Util.arrow_formals t in
                     (match uu____2100 with
                      | (f,uu____2116) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2238::uu____2239) ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Too many pattern arguments",
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                            | (uu____2290::uu____2291,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2369  ->
                                        match uu____2369 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2396 =
                                                     let uu____2399 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2399 in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2396
                                                     FStar_Syntax_Syntax.tun in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                 let uu____2401 =
                                                   maybe_dot inaccessible a r in
                                                 (uu____2401, true)
                                             | uu____2406 ->
                                                 let uu____2409 =
                                                   let uu____2410 =
                                                     let uu____2415 =
                                                       let uu____2416 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.format1
                                                         "Insufficient pattern arguments (%s)"
                                                         uu____2416 in
                                                     (uu____2415,
                                                       (FStar_Ident.range_of_lid
                                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                   FStar_Errors.Error
                                                     uu____2410 in
                                                 FStar_Exn.raise uu____2409)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2490,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2491)) when p_imp ->
                                     let uu____2494 = aux formals' pats' in
                                     (p2, true) :: uu____2494
                                 | (uu____2511,FStar_Pervasives_Native.Some
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
                                     let uu____2519 = aux formals' pats2 in
                                     (p3, true) :: uu____2519
                                 | (uu____2536,imp) ->
                                     let uu____2542 =
                                       let uu____2549 =
                                         FStar_Syntax_Syntax.is_implicit imp in
                                       (p2, uu____2549) in
                                     let uu____2552 = aux formals' pats' in
                                     uu____2542 :: uu____2552) in
                          let uu___291_2567 = p1 in
                          let uu____2570 =
                            let uu____2571 =
                              let uu____2584 = aux f pats1 in
                              (fv, uu____2584) in
                            FStar_Syntax_Syntax.Pat_cons uu____2571 in
                          {
                            FStar_Syntax_Syntax.v = uu____2570;
                            FStar_Syntax_Syntax.p =
                              (uu___291_2567.FStar_Syntax_Syntax.p)
                          }))
            | uu____2601 -> p1 in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu____2637 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
            match uu____2637 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2695 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu____2695 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2721 =
                       let uu____2722 =
                         let uu____2727 =
                           FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                         (uu____2727, (p3.FStar_Syntax_Syntax.p)) in
                       FStar_Errors.Error uu____2722 in
                     FStar_Exn.raise uu____2721
                 | uu____2746 -> (b, a, w, arg, guard, p3)) in
          let uu____2755 = one_pat true env p in
          match uu____2755 with
          | (b,uu____2785,uu____2786,tm,guard,p1) -> (b, tm, guard, p1)
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
          | (uu____2832,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2834)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2839,uu____2840) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2844 =
                    let uu____2845 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2846 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2845 uu____2846 in
                  failwith uu____2844)
               else ();
               (let uu____2849 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2849
                then
                  let uu____2850 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2851 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2850
                    uu____2851
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___292_2855 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___292_2855.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___292_2855.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2859 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2859
                then
                  let uu____2860 =
                    let uu____2861 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2862 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2861 uu____2862 in
                  failwith uu____2860
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___293_2866 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___293_2866.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___293_2866.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2868),uu____2869) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2891 =
                  let uu____2892 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2892 in
                if uu____2891
                then
                  let uu____2893 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2893
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2912;
                FStar_Syntax_Syntax.vars = uu____2913;_},args))
              ->
              ((let uu____2952 =
                  let uu____2953 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2953 Prims.op_Negation in
                if uu____2952
                then
                  let uu____2954 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2954
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3090)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3165) ->
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
                       | ((e2,imp),uu____3202) ->
                           let pat =
                             let uu____3224 = aux argpat e2 in
                             let uu____3225 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3224, uu____3225) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3230 ->
                      let uu____3253 =
                        let uu____3254 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3255 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3254 uu____3255 in
                      failwith uu____3253 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3267;
                     FStar_Syntax_Syntax.vars = uu____3268;_},uu____3269);
                FStar_Syntax_Syntax.pos = uu____3270;
                FStar_Syntax_Syntax.vars = uu____3271;_},args))
              ->
              ((let uu____3314 =
                  let uu____3315 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3315 Prims.op_Negation in
                if uu____3314
                then
                  let uu____3316 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3316
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3452)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3527) ->
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
                       | ((e2,imp),uu____3564) ->
                           let pat =
                             let uu____3586 = aux argpat e2 in
                             let uu____3587 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3586, uu____3587) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3592 ->
                      let uu____3615 =
                        let uu____3616 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3617 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3616 uu____3617 in
                      failwith uu____3615 in
                match_args [] args argpats))
          | uu____3626 ->
              let uu____3631 =
                let uu____3632 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3633 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3634 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3632 uu____3633 uu____3634 in
              failwith uu____3631 in
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
    let pat_as_arg uu____3671 =
      match uu____3671 with
      | (p,i) ->
          let uu____3688 = decorated_pattern_as_term p in
          (match uu____3688 with
           | (vars,te) ->
               let uu____3711 =
                 let uu____3716 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3716) in
               (vars, uu____3711)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3730 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3730)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3734 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3734)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3738 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3738)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3759 =
          let uu____3774 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3774 FStar_List.unzip in
        (match uu____3759 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3884 =
               let uu____3885 =
                 let uu____3886 =
                   let uu____3901 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3901, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3886 in
               mk1 uu____3885 in
             (vars1, uu____3884))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3941)::[] -> wp
      | uu____3958 ->
          let uu____3967 =
            let uu____3968 =
              let uu____3969 =
                FStar_List.map
                  (fun uu____3979  ->
                     match uu____3979 with
                     | (x,uu____3985) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3969 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3968 in
          failwith uu____3967 in
    let uu____3990 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3990, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4004 = destruct_comp c in
        match uu____4004 with
        | (u,uu____4012,wp) ->
            let uu____4014 =
              let uu____4023 =
                let uu____4024 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____4024 in
              [uu____4023] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4014;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4034 =
          let uu____4041 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____4042 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____4041 uu____4042 in
        match uu____4034 with | (m,uu____4044,uu____4045) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4055 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____4055
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
        let uu____4092 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4092 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4129 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4129 with
             | (a,kwp) ->
                 let uu____4160 = destruct_comp m1 in
                 let uu____4167 = destruct_comp m2 in
                 ((md, a, kwp), uu____4160, uu____4167))
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
            let uu____4229 =
              let uu____4230 =
                let uu____4239 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4239] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4230;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4229
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
      let uu___294_4278 = lc in
      let uu____4279 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___294_4278.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4279;
        FStar_Syntax_Syntax.cflags =
          (uu___294_4278.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4284  ->
             let uu____4285 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4285)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4289 =
      let uu____4290 = FStar_Syntax_Subst.compress t in
      uu____4290.FStar_Syntax_Syntax.n in
    match uu____4289 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4293 -> true
    | uu____4306 -> false
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
              let uu____4344 =
                let uu____4345 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4345 in
              if uu____4344
              then f
              else (let uu____4347 = reason1 () in label uu____4347 r f)
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
            let uu___295_4358 = g in
            let uu____4359 =
              let uu____4360 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4360 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4359;
              FStar_TypeChecker_Env.deferred =
                (uu___295_4358.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___295_4358.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___295_4358.FStar_TypeChecker_Env.implicits)
            }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4374 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4374
        then c
        else
          (let uu____4376 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4376
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4415 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4415] in
                       let us =
                         let uu____4419 =
                           let uu____4422 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4422] in
                         u_res :: uu____4419 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4426 =
                         let uu____4427 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4428 =
                           let uu____4429 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4430 =
                             let uu____4433 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4434 =
                               let uu____4437 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4437] in
                             uu____4433 :: uu____4434 in
                           uu____4429 :: uu____4430 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4427 uu____4428 in
                       uu____4426 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4441 = destruct_comp c1 in
              match uu____4441 with
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
        let close1 uu____4469 =
          let uu____4470 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4470 in
        let uu___296_4471 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___296_4471.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___296_4471.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___296_4471.FStar_Syntax_Syntax.cflags);
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
          let uu____4482 =
            let uu____4483 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4483 in
          if uu____4482
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let uu____4485 = FStar_Syntax_Util.is_unit t in
             if uu____4485
             then
               FStar_Syntax_Syntax.mk_Total' t
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
             else
               (let m =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Parser_Const.effect_PURE_lid in
                let u_t = env.FStar_TypeChecker_Env.universe_of env t in
                let wp =
                  let uu____4490 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____4490
                  then FStar_Syntax_Syntax.tun
                  else
                    (let uu____4492 =
                       FStar_TypeChecker_Env.wp_signature env
                         FStar_Parser_Const.effect_PURE_lid in
                     match uu____4492 with
                     | (a,kwp) ->
                         let k =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (a, t)] kwp in
                         let uu____4500 =
                           let uu____4501 =
                             let uu____4502 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                             let uu____4503 =
                               let uu____4504 = FStar_Syntax_Syntax.as_arg t in
                               let uu____4505 =
                                 let uu____4508 =
                                   FStar_Syntax_Syntax.as_arg v1 in
                                 [uu____4508] in
                               uu____4504 :: uu____4505 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____4502
                               uu____4503 in
                           uu____4501 FStar_Pervasives_Native.None
                             v1.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.NoFullNorm] env
                           uu____4500) in
                mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
        (let uu____4512 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4512
         then
           let uu____4513 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4514 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4515 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4513
             uu____4514 uu____4515
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
          fun uu____4533  ->
            match uu____4533 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4546 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4546
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4549 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4551 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4552 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4549 uu____4551 bstr uu____4552
                  else ());
                 (let bind_it uu____4557 =
                    let uu____4558 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4558
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4568 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4568
                        then
                          let uu____4569 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4571 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4572 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4573 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4574 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4569 uu____4571 uu____4572 uu____4573
                            uu____4574
                        else ());
                       (let aux uu____4589 =
                          let uu____4590 = FStar_Syntax_Util.is_trivial_wp c1 in
                          if uu____4590
                          then
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Util.Inl (c2, "trivial no binder")
                            | FStar_Pervasives_Native.Some uu____4619 ->
                                let uu____4620 =
                                  FStar_Syntax_Util.is_ml_comp c2 in
                                (if uu____4620
                                 then FStar_Util.Inl (c2, "trivial ml")
                                 else
                                   FStar_Util.Inr
                                     "c1 trivial; but c2 is not ML")
                          else
                            (let uu____4647 =
                               (FStar_Syntax_Util.is_ml_comp c1) &&
                                 (FStar_Syntax_Util.is_ml_comp c2) in
                             if uu____4647
                             then FStar_Util.Inl (c2, "both ml")
                             else
                               FStar_Util.Inr
                                 "c1 not trivial, and both are not ML") in
                        let subst_c2 reason =
                          match (e1opt, b) with
                          | (FStar_Pervasives_Native.Some
                             e,FStar_Pervasives_Native.Some x) ->
                              let uu____4703 =
                                let uu____4708 =
                                  FStar_Syntax_Subst.subst_comp
                                    [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                (uu____4708, reason) in
                              FStar_Util.Inl uu____4703
                          | uu____4713 -> aux () in
                        let try_simplify uu____4735 =
                          let rec maybe_close t x c =
                            let uu____4746 =
                              let uu____4747 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4747.FStar_Syntax_Syntax.n in
                            match uu____4746 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4751) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4757 -> c in
                          let uu____4758 =
                            let uu____4759 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4759 in
                          if uu____4758
                          then
                            let uu____4772 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4772
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4792 =
                                  let uu____4793 =
                                    let uu____4798 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4798) in
                                  FStar_Errors.Error uu____4793 in
                                FStar_Exn.raise uu____4792))
                          else
                            (let uu____4810 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4810
                             then subst_c2 "both total"
                             else
                               (let uu____4822 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4822
                                then
                                  let uu____4833 =
                                    let uu____4838 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4838, "both gtot") in
                                  FStar_Util.Inl uu____4833
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4864 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4866 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4866) in
                                       if uu____4864
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___297_4879 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___297_4879.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___297_4879.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4880 =
                                           let uu____4885 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4885, "c1 Tot") in
                                         FStar_Util.Inl uu____4880
                                       else aux ()
                                   | uu____4891 -> aux ()))) in
                        let uu____4900 = try_simplify () in
                        match uu____4900 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4924 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4924
                              then
                                let uu____4925 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4926 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4927 =
                                  FStar_Syntax_Print.comp_to_string c in
                                let uu____4928 =
                                  FStar_Syntax_Print.lid_to_string joined_eff in
                                FStar_Util.print5
                                  "Simplified (because %s) bind c1: %s\n\nc2: %s\n\nto c: %s\n\nWith effect lid: %s\n\n"
                                  reason uu____4925 uu____4926 uu____4927
                                  uu____4928
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let c21 =
                              let uu____4938 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                              if uu____4938
                              then
                                match (e1opt, b) with
                                | (FStar_Pervasives_Native.Some
                                   e,FStar_Pervasives_Native.Some bv) ->
                                    let uu____4949 =
                                      subst_c2 "inline all pure" in
                                    (match uu____4949 with
                                     | FStar_Util.Inl (c21,uu____4959) ->
                                         let c2_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c21 in
                                         let uu____4965 =
                                           destruct_comp c2_typ in
                                         (match uu____4965 with
                                          | (u_res_t,res_t,wp) ->
                                              let md =
                                                FStar_TypeChecker_Env.get_effect_decl
                                                  env
                                                  c2_typ.FStar_Syntax_Syntax.effect_name in
                                              let c1_typ =
                                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                                  env c1 in
                                              let uu____4977 =
                                                destruct_comp c1_typ in
                                              (match uu____4977 with
                                               | (u_res_t1,res_t1,uu____4986)
                                                   ->
                                                   let wp1 =
                                                     let uu____4990 =
                                                       let uu____4991 =
                                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                                           [u_res_t] env md
                                                           md.FStar_Syntax_Syntax.assume_p in
                                                       let uu____4992 =
                                                         let uu____4993 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             res_t in
                                                         let uu____4994 =
                                                           let uu____4997 =
                                                             let uu____4998 =
                                                               let uu____4999
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   bv in
                                                               FStar_Syntax_Util.mk_eq2
                                                                 u_res_t1
                                                                 res_t1
                                                                 uu____4999 e in
                                                             FStar_Syntax_Syntax.as_arg
                                                               uu____4998 in
                                                           let uu____5000 =
                                                             let uu____5003 =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 wp in
                                                             [uu____5003] in
                                                           uu____4997 ::
                                                             uu____5000 in
                                                         uu____4993 ::
                                                           uu____4994 in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____4991
                                                         uu____4992 in
                                                     uu____4990
                                                       FStar_Pervasives_Native.None
                                                       wp.FStar_Syntax_Syntax.pos in
                                                   mk_comp md u_res_t res_t
                                                     wp1
                                                     c2_typ.FStar_Syntax_Syntax.flags))
                                     | FStar_Util.Inr uu____5006 -> c2)
                                | (uu____5011,uu____5012) -> c2
                              else c2 in
                            let uu____5022 = lift_and_destruct env c1 c21 in
                            (match uu____5022 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5079 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____5079]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____5081 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____5081] in
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
                                   let uu____5094 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____5095 =
                                     let uu____5098 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____5099 =
                                       let uu____5102 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____5103 =
                                         let uu____5106 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____5107 =
                                           let uu____5110 =
                                             let uu____5111 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____5111 in
                                           [uu____5110] in
                                         uu____5106 :: uu____5107 in
                                       uu____5102 :: uu____5103 in
                                     uu____5098 :: uu____5099 in
                                   uu____5094 :: uu____5095 in
                                 let wp =
                                   let uu____5115 =
                                     let uu____5116 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____5116
                                       wp_args in
                                   uu____5115 FStar_Pervasives_Native.None
                                     t2.FStar_Syntax_Syntax.pos in
                                 mk_comp md u_t2 t2 wp []))) in
                  {
                    FStar_Syntax_Syntax.eff_name = joined_eff;
                    FStar_Syntax_Syntax.res_typ =
                      (lc21.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = [];
                    FStar_Syntax_Syntax.comp = bind_it
                  }))
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
      | uu____5128 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5147 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5151 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5151
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5158 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5158
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5163 = destruct_comp c1 in
                    match uu____5163 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5179 =
                            let uu____5180 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5181 =
                              let uu____5182 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5183 =
                                let uu____5186 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5187 =
                                  let uu____5190 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5190] in
                                uu____5186 :: uu____5187 in
                              uu____5182 :: uu____5183 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5180
                              uu____5181 in
                          uu____5179 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___298_5193 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___298_5193.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___298_5193.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___298_5193.FStar_Syntax_Syntax.cflags);
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
            let uu____5226 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5226
            then (lc, g0)
            else
              ((let uu____5233 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5233
                then
                  let uu____5234 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5235 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5234 uu____5235
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___267_5245  ->
                          match uu___267_5245 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5248 -> [])) in
                let strengthen uu____5254 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5262 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5262 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5269 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5271 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5271) in
                           if uu____5269
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5278 =
                                 let uu____5279 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5279 in
                               FStar_Syntax_Util.comp_set_flags uu____5278
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5285 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5285
                           then
                             let uu____5286 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5287 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5286 uu____5287
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5290 = destruct_comp c2 in
                           match uu____5290 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5306 =
                                   let uu____5307 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5308 =
                                     let uu____5309 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5310 =
                                       let uu____5313 =
                                         let uu____5314 =
                                           let uu____5315 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5315 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5314 in
                                       let uu____5316 =
                                         let uu____5319 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5319] in
                                       uu____5313 :: uu____5316 in
                                     uu____5309 :: uu____5310 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5307
                                     uu____5308 in
                                 uu____5306 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5323 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5323
                                 then
                                   let uu____5324 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5324
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5327 =
                  let uu___299_5328 = lc in
                  let uu____5329 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5330 =
                    let uu____5333 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5335 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5335) in
                    if uu____5333 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5329;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___299_5328.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5330;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5327,
                  (let uu___300_5340 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___300_5340.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___300_5340.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___300_5340.FStar_TypeChecker_Env.implicits)
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
        let uu____5355 =
          let uu____5360 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5361 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5360, uu____5361) in
        match uu____5355 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5370 =
                let uu____5371 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5372 =
                  let uu____5373 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5374 =
                    let uu____5377 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5377] in
                  uu____5373 :: uu____5374 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5371 uu____5372 in
              uu____5370 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5383 =
                let uu____5384 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5385 =
                  let uu____5386 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5387 =
                    let uu____5390 =
                      let uu____5391 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5391 in
                    let uu____5392 =
                      let uu____5395 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5395] in
                    uu____5390 :: uu____5392 in
                  uu____5386 :: uu____5387 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5384 uu____5385 in
              uu____5383 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5401 =
                let uu____5402 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5403 =
                  let uu____5404 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5405 =
                    let uu____5408 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5409 =
                      let uu____5412 =
                        let uu____5413 =
                          let uu____5414 =
                            let uu____5415 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5415] in
                          FStar_Syntax_Util.abs uu____5414 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5413 in
                      [uu____5412] in
                    uu____5408 :: uu____5409 in
                  uu____5404 :: uu____5405 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5402 uu____5403 in
              uu____5401 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5422 = FStar_TypeChecker_Env.get_range env in
              bind uu____5422 env FStar_Pervasives_Native.None
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
          let comp uu____5441 =
            let uu____5442 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5442
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5445 =
                 let uu____5470 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5471 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5470 uu____5471 in
               match uu____5445 with
               | ((md,uu____5473,uu____5474),(u_res_t,res_t,wp_then),
                  (uu____5478,uu____5479,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5517 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5518 =
                       let uu____5519 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5520 =
                         let uu____5521 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5522 =
                           let uu____5525 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5526 =
                             let uu____5529 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5530 =
                               let uu____5533 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5533] in
                             uu____5529 :: uu____5530 in
                           uu____5525 :: uu____5526 in
                         uu____5521 :: uu____5522 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5519 uu____5520 in
                     uu____5518 FStar_Pervasives_Native.None uu____5517 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5539 =
                     let uu____5540 = FStar_Options.split_cases () in
                     uu____5540 > (Prims.parse_int "0") in
                   if uu____5539
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5546 =
                          let uu____5547 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5548 =
                            let uu____5549 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5550 =
                              let uu____5553 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5553] in
                            uu____5549 :: uu____5550 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5547 uu____5548 in
                        uu____5546 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5556 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5556;
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
      let uu____5563 =
        let uu____5564 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5564 in
      FStar_Syntax_Syntax.fvar uu____5563 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5596  ->
                 match uu____5596 with
                 | (uu____5601,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5606 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5608 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5608
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5628 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5629 =
                 let uu____5630 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5631 =
                   let uu____5632 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5633 =
                     let uu____5636 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5637 =
                       let uu____5640 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5641 =
                         let uu____5644 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5644] in
                       uu____5640 :: uu____5641 in
                     uu____5636 :: uu____5637 in
                   uu____5632 :: uu____5633 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5630 uu____5631 in
               uu____5629 FStar_Pervasives_Native.None uu____5628 in
             let default_case =
               let post_k =
                 let uu____5651 =
                   let uu____5658 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5658] in
                 let uu____5659 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5651 uu____5659 in
               let kwp =
                 let uu____5665 =
                   let uu____5672 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5672] in
                 let uu____5673 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5665 uu____5673 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5678 =
                   let uu____5679 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5679] in
                 let uu____5680 =
                   let uu____5681 =
                     let uu____5684 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5684 in
                   let uu____5685 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5681 uu____5685 in
                 FStar_Syntax_Util.abs uu____5678 uu____5680
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
                 (fun uu____5709  ->
                    fun celse  ->
                      match uu____5709 with
                      | (g,cthen) ->
                          let uu____5717 =
                            let uu____5742 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5742 celse in
                          (match uu____5717 with
                           | ((md,uu____5744,uu____5745),(uu____5746,uu____5747,wp_then),
                              (uu____5749,uu____5750,wp_else)) ->
                               let uu____5770 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5770 []))
                 lcases default_case in
             let uu____5771 =
               let uu____5772 = FStar_Options.split_cases () in
               uu____5772 > (Prims.parse_int "0") in
             if uu____5771
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5776 = destruct_comp comp1 in
                match uu____5776 with
                | (uu____5783,uu____5784,wp) ->
                    let wp1 =
                      let uu____5789 =
                        let uu____5790 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5791 =
                          let uu____5792 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5793 =
                            let uu____5796 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5796] in
                          uu____5792 :: uu____5793 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5790 uu____5791 in
                      uu____5789 FStar_Pervasives_Native.None
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
          let uu____5811 =
            ((let uu____5814 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5814) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5816 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5816) in
          if uu____5811
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5825 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5829 =
            ((let uu____5832 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5832) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5829
          then c
          else
            (let uu____5836 = FStar_Syntax_Util.is_partial_return c in
             if uu____5836
             then c
             else
               (let uu____5840 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5840
                then
                  let uu____5843 =
                    let uu____5844 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5844 in
                  (if uu____5843
                   then
                     let uu____5847 =
                       let uu____5848 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5849 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5848 uu____5849 in
                     failwith uu____5847
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5854 =
                        let uu____5855 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5855 in
                      if uu____5854
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___301_5860 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___301_5860.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___301_5860.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___301_5860.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5871 =
                       let uu____5874 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5874
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5871 in
                   let eq1 =
                     let uu____5878 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5878 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5880 =
                     let uu____5881 =
                       let uu____5886 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5886.FStar_Syntax_Syntax.comp in
                     uu____5881 () in
                   FStar_Syntax_Util.comp_set_flags uu____5880 flags))) in
        let uu____5889 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____5889
        then lc
        else
          (let uu___302_5891 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___302_5891.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___302_5891.FStar_Syntax_Syntax.res_typ);
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
          let uu____5916 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5916 with
          | FStar_Pervasives_Native.None  ->
              let uu____5925 =
                let uu____5926 =
                  let uu____5931 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5932 = FStar_TypeChecker_Env.get_range env in
                  (uu____5931, uu____5932) in
                FStar_Errors.Error uu____5926 in
              FStar_Exn.raise uu____5925
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
            let uu____5965 =
              let uu____5966 = FStar_Syntax_Subst.compress t2 in
              uu____5966.FStar_Syntax_Syntax.n in
            match uu____5965 with
            | FStar_Syntax_Syntax.Tm_type uu____5969 -> true
            | uu____5970 -> false in
          let uu____5971 =
            let uu____5972 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5972.FStar_Syntax_Syntax.n in
          match uu____5971 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5980 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5991 =
                  let uu____5992 =
                    let uu____5993 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5993 in
                  (FStar_Pervasives_Native.None, uu____5992) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5991 in
              let e1 =
                let uu____6003 =
                  let uu____6004 =
                    let uu____6005 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6005] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6004 in
                uu____6003 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6010 -> (e, lc)
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
              (let uu____6039 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6039 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6062 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6084 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6084, false)
            else
              (let uu____6090 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6090, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6101) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6110 =
                  let uu____6111 =
                    let uu____6116 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6116, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6111 in
                FStar_Exn.raise uu____6110
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___303_6126 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___303_6126.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___303_6126.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___303_6126.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6131 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6131 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___304_6139 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___304_6139.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___304_6139.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___304_6139.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___305_6142 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___305_6142.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___305_6142.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___305_6142.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6148 =
                     let uu____6149 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6149
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6154 =
                          let uu____6155 = FStar_Syntax_Subst.compress f1 in
                          uu____6155.FStar_Syntax_Syntax.n in
                        match uu____6154 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6160,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6162;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6163;_},uu____6164)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___306_6186 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___306_6186.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___306_6186.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___306_6186.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6187 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6192 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6192
                              then
                                let uu____6193 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6194 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6195 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6196 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6193 uu____6194 uu____6195 uu____6196
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6199 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6199 with
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
                                  let uu____6212 = destruct_comp ct in
                                  (match uu____6212 with
                                   | (u_t,uu____6222,uu____6223) ->
                                       let wp =
                                         let uu____6227 =
                                           let uu____6228 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6229 =
                                             let uu____6230 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6231 =
                                               let uu____6234 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6234] in
                                             uu____6230 :: uu____6231 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6228 uu____6229 in
                                         uu____6227
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6238 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6238 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6248 =
                                             let uu____6249 =
                                               let uu____6250 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6250] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6249 in
                                           uu____6248
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6254 =
                                         let uu____6259 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6272 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6273 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6259
                                           uu____6272 e cret uu____6273 in
                                       (match uu____6254 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___307_6279 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___307_6279.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___307_6279.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6281 =
                                                let uu____6282 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6282 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6281
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6293 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6293
                                              then
                                                let uu____6294 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6294
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___268_6304  ->
                             match uu___268_6304 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6307 -> [])) in
                   let lc1 =
                     let uu___308_6309 = lc in
                     let uu____6310 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6310;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___309_6312 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___309_6312.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___309_6312.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___309_6312.FStar_TypeChecker_Env.implicits)
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
        let uu____6335 =
          let uu____6336 =
            let uu____6337 =
              let uu____6338 =
                let uu____6339 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6339 in
              [uu____6338] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6337 in
          uu____6336 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6335 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6346 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6346
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6364 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6379 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6408)::(ens,uu____6410)::uu____6411 ->
                    let uu____6440 =
                      let uu____6443 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6443 in
                    let uu____6444 =
                      let uu____6445 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6445 in
                    (uu____6440, uu____6444)
                | uu____6448 ->
                    let uu____6457 =
                      let uu____6458 =
                        let uu____6463 =
                          let uu____6464 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6464 in
                        (uu____6463, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6458 in
                    FStar_Exn.raise uu____6457)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6480)::uu____6481 ->
                    let uu____6500 =
                      let uu____6505 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6505 in
                    (match uu____6500 with
                     | (us_r,uu____6537) ->
                         let uu____6538 =
                           let uu____6543 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6543 in
                         (match uu____6538 with
                          | (us_e,uu____6575) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6578 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6578
                                  us_r in
                              let as_ens =
                                let uu____6580 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6580
                                  us_e in
                              let req =
                                let uu____6584 =
                                  let uu____6585 =
                                    let uu____6586 =
                                      let uu____6597 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6597] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6586 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6585 in
                                uu____6584 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6615 =
                                  let uu____6616 =
                                    let uu____6617 =
                                      let uu____6628 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6628] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6617 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6616 in
                                uu____6615 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6643 =
                                let uu____6646 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6646 in
                              let uu____6647 =
                                let uu____6648 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6648 in
                              (uu____6643, uu____6647)))
                | uu____6651 -> failwith "Impossible"))
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
      (let uu____6677 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6677
       then
         let uu____6678 = FStar_Syntax_Print.term_to_string tm in
         let uu____6679 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6678 uu____6679
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
        (let uu____6697 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6697
         then
           let uu____6698 = FStar_Syntax_Print.term_to_string tm in
           let uu____6699 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6698
             uu____6699
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6704 =
      let uu____6705 =
        let uu____6706 = FStar_Syntax_Subst.compress t in
        uu____6706.FStar_Syntax_Syntax.n in
      match uu____6705 with
      | FStar_Syntax_Syntax.Tm_app uu____6709 -> false
      | uu____6724 -> true in
    if uu____6704
    then t
    else
      (let uu____6726 = FStar_Syntax_Util.head_and_args t in
       match uu____6726 with
       | (head1,args) ->
           let uu____6763 =
             let uu____6764 =
               let uu____6765 = FStar_Syntax_Subst.compress head1 in
               uu____6765.FStar_Syntax_Syntax.n in
             match uu____6764 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6768 -> false in
           if uu____6763
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6790 ->
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
             let uu____6827 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6827 with
             | (formals,uu____6841) ->
                 let n_implicits =
                   let uu____6859 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6935  ->
                             match uu____6935 with
                             | (uu____6942,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6859 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7073 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7073 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7097 =
                     let uu____7098 =
                       let uu____7103 =
                         let uu____7104 = FStar_Util.string_of_int n_expected in
                         let uu____7111 = FStar_Syntax_Print.term_to_string e in
                         let uu____7112 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7104 uu____7111 uu____7112 in
                       let uu____7119 = FStar_TypeChecker_Env.get_range env in
                       (uu____7103, uu____7119) in
                     FStar_Errors.Error uu____7098 in
                   FStar_Exn.raise uu____7097
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___269_7140 =
             match uu___269_7140 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7170 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7170 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7279) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7322,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7355 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7355 with
                           | (v1,uu____7395,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7412 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7412 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7505 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7505)))
                      | (uu____7532,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7578 =
                      let uu____7605 = inst_n_binders t in
                      aux [] uu____7605 bs1 in
                    (match uu____7578 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7676) -> (e, torig, guard)
                          | (uu____7707,[]) when
                              let uu____7738 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7738 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7739 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7771 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7786 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7794 =
      let uu____7797 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7797
        (FStar_List.map
           (fun u  ->
              let uu____7807 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7807 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7794 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7824 = FStar_Util.set_is_empty x in
      if uu____7824
      then []
      else
        (let s =
           let uu____7831 =
             let uu____7834 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7834 in
           FStar_All.pipe_right uu____7831 FStar_Util.set_elements in
         (let uu____7842 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7842
          then
            let uu____7843 =
              let uu____7844 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7844 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7843
          else ());
         (let r =
            let uu____7851 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7851 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7866 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7866
                     then
                       let uu____7867 =
                         let uu____7868 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7868 in
                       let uu____7869 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7870 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7867 uu____7869 uu____7870
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
        let uu____7892 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7892 FStar_Util.fifo_set_elements in
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
        | ([],uu____7924) -> generalized_univ_names
        | (uu____7931,[]) -> explicit_univ_names
        | uu____7938 ->
            let uu____7947 =
              let uu____7948 =
                let uu____7953 =
                  let uu____7954 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7954 in
                (uu____7953, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7948 in
            FStar_Exn.raise uu____7947
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
      (let uu____7971 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7971
       then
         let uu____7972 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7972
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7978 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7978
        then
          let uu____7979 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7979
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
        let uu____8049 =
          let uu____8050 =
            FStar_Util.for_all
              (fun uu____8063  ->
                 match uu____8063 with
                 | (uu____8072,uu____8073,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8050 in
        if uu____8049
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8119 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8119
              then
                let uu____8120 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8120
              else ());
             (let c1 =
                let uu____8123 = FStar_TypeChecker_Env.should_verify env in
                if uu____8123
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
              (let uu____8126 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8126
               then
                 let uu____8127 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8127
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8188 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8188 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8318 =
             match uu____8318 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8384 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8384
                   then
                     let uu____8385 =
                       let uu____8386 =
                         let uu____8389 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8389
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8386
                         (FStar_String.concat ", ") in
                     let uu____8416 =
                       let uu____8417 =
                         let uu____8420 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8420
                           (FStar_List.map
                              (fun uu____8448  ->
                                 match uu____8448 with
                                 | (u,t2) ->
                                     let uu____8455 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8456 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8455 uu____8456)) in
                       FStar_All.pipe_right uu____8417
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8385
                       uu____8416
                   else ());
                  (let univs2 =
                     let uu____8463 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8486  ->
                            match uu____8486 with
                            | (uu____8495,t2) ->
                                let uu____8497 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8497)
                       univs1 uu____8463 in
                   let uvs = gen_uvars uvt in
                   (let uu____8520 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8520
                    then
                      let uu____8521 =
                        let uu____8522 =
                          let uu____8525 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8525
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8522
                          (FStar_String.concat ", ") in
                      let uu____8552 =
                        let uu____8553 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8585  ->
                                  match uu____8585 with
                                  | (u,t2) ->
                                      let uu____8592 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8593 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8592 uu____8593)) in
                        FStar_All.pipe_right uu____8553
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8521
                        uu____8552
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8623 =
             let uu____8656 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8656 in
           match uu____8623 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8774 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8774
                 then ()
                 else
                   (let uu____8776 = lec_hd in
                    match uu____8776 with
                    | (lb1,uu____8784,uu____8785) ->
                        let uu____8786 = lec2 in
                        (match uu____8786 with
                         | (lb2,uu____8794,uu____8795) ->
                             let msg =
                               let uu____8797 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8798 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8797 uu____8798 in
                             let uu____8799 =
                               let uu____8800 =
                                 let uu____8805 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8805) in
                               FStar_Errors.Error uu____8800 in
                             FStar_Exn.raise uu____8799)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8916  ->
                           match uu____8916 with
                           | (u,uu____8924) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8946  ->
                                       match uu____8946 with
                                       | (u',uu____8954) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8959 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8959
                 then ()
                 else
                   (let uu____8961 = lec_hd in
                    match uu____8961 with
                    | (lb1,uu____8969,uu____8970) ->
                        let uu____8971 = lec2 in
                        (match uu____8971 with
                         | (lb2,uu____8979,uu____8980) ->
                             let msg =
                               let uu____8982 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8983 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8982 uu____8983 in
                             let uu____8984 =
                               let uu____8985 =
                                 let uu____8990 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8990) in
                               FStar_Errors.Error uu____8985 in
                             FStar_Exn.raise uu____8984)) in
               let lecs1 =
                 let uu____9000 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9059 = univs_and_uvars_of_lec this_lec in
                        match uu____9059 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9000 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9212 = lec_hd in
                   match uu____9212 with
                   | (lbname,e,c) ->
                       let uu____9222 =
                         let uu____9223 =
                           let uu____9228 =
                             let uu____9229 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9230 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9231 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9229 uu____9230 uu____9231 in
                           let uu____9232 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9228, uu____9232) in
                         FStar_Errors.Error uu____9223 in
                       FStar_Exn.raise uu____9222 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9262  ->
                         match uu____9262 with
                         | (u,k) ->
                             let uu____9275 = FStar_Syntax_Unionfind.find u in
                             (match uu____9275 with
                              | FStar_Pervasives_Native.Some uu____9284 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9291 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9295 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9295 with
                                   | (bs,kres) ->
                                       ((let uu____9333 =
                                           let uu____9334 =
                                             let uu____9337 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9337 in
                                           uu____9334.FStar_Syntax_Syntax.n in
                                         match uu____9333 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9338 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9342 =
                                               let uu____9343 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9343 in
                                             if uu____9342
                                             then fail kres
                                             else ()
                                         | uu____9345 -> fail kres);
                                        (let a =
                                           let uu____9347 =
                                             let uu____9350 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9350 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9347 kres in
                                         let t =
                                           let uu____9354 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9354
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
                      (fun uu____9473  ->
                         match uu____9473 with
                         | (lbname,e,c) ->
                             let uu____9519 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9588 ->
                                   let uu____9603 = (e, c) in
                                   (match uu____9603 with
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
                                                (fun uu____9640  ->
                                                   match uu____9640 with
                                                   | (x,uu____9648) ->
                                                       let uu____9653 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9653)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9663 =
                                                let uu____9664 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9664 in
                                              if uu____9663
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
                                          let uu____9672 =
                                            let uu____9673 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9673.FStar_Syntax_Syntax.n in
                                          match uu____9672 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9696 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9696 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9711 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9713 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9713, gen_tvars)) in
                             (match uu____9519 with
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
        (let uu____9859 = Obj.magic () in ());
        (let uu____9861 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9861
         then
           let uu____9862 =
             let uu____9863 =
               FStar_List.map
                 (fun uu____9876  ->
                    match uu____9876 with
                    | (lb,uu____9884,uu____9885) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9863 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9862
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9906  ->
                match uu____9906 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9935 = gen env is_rec lecs in
           match uu____9935 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10034  ->
                       match uu____10034 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10096 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10096
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10140  ->
                           match uu____10140 with
                           | (l,us,e,c,gvs) ->
                               let uu____10174 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10175 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10176 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10177 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10178 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10174 uu____10175 uu____10176
                                 uu____10177 uu____10178))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10219  ->
                match uu____10219 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10263 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10263, t, c, gvs)) univnames_lecs
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
              (let uu____10306 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10306 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10312 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10312) in
          let is_var e1 =
            let uu____10319 =
              let uu____10320 = FStar_Syntax_Subst.compress e1 in
              uu____10320.FStar_Syntax_Syntax.n in
            match uu____10319 with
            | FStar_Syntax_Syntax.Tm_name uu____10323 -> true
            | uu____10324 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___310_10340 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___310_10340.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___310_10340.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10341 -> e2 in
          let env2 =
            let uu___311_10343 = env1 in
            let uu____10344 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___311_10343.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___311_10343.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___311_10343.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___311_10343.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___311_10343.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___311_10343.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___311_10343.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___311_10343.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___311_10343.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___311_10343.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___311_10343.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___311_10343.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___311_10343.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___311_10343.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___311_10343.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10344;
              FStar_TypeChecker_Env.is_iface =
                (uu___311_10343.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___311_10343.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___311_10343.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___311_10343.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___311_10343.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___311_10343.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___311_10343.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___311_10343.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___311_10343.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___311_10343.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___311_10343.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___311_10343.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___311_10343.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___311_10343.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___311_10343.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___311_10343.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___311_10343.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___311_10343.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10345 = check env2 t1 t2 in
          match uu____10345 with
          | FStar_Pervasives_Native.None  ->
              let uu____10352 =
                let uu____10353 =
                  let uu____10358 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10359 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10358, uu____10359) in
                FStar_Errors.Error uu____10353 in
              FStar_Exn.raise uu____10352
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10366 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10366
                then
                  let uu____10367 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10367
                else ());
               (let uu____10369 = decorate e t2 in (uu____10369, g)))
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
        let uu____10397 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10397
        then
          let uu____10402 = discharge g1 in
          let uu____10403 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10402, uu____10403)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10416 =
               let uu____10417 =
                 let uu____10418 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10418 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10417
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10416
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10420 = destruct_comp c1 in
           match uu____10420 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10437 = FStar_TypeChecker_Env.get_range env in
                 let uu____10438 =
                   let uu____10439 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10440 =
                     let uu____10441 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10442 =
                       let uu____10445 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10445] in
                     uu____10441 :: uu____10442 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10439 uu____10440 in
                 uu____10438 FStar_Pervasives_Native.None uu____10437 in
               ((let uu____10449 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10449
                 then
                   let uu____10450 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10450
                 else ());
                (let g2 =
                   let uu____10453 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10453 in
                 let uu____10454 = discharge g2 in
                 let uu____10455 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10454, uu____10455))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___270_10479 =
        match uu___270_10479 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10487)::[] -> f fst1
        | uu____10504 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10509 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10509
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10518 =
          let uu____10521 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10521 in
        FStar_All.pipe_right uu____10518
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10532 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10532
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___271_10546 =
        match uu___271_10546 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10554)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10573)::[] ->
            let uu____10602 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10602
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10607 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10617 =
          let uu____10624 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10624) in
        let uu____10629 =
          let uu____10638 =
            let uu____10645 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10645) in
          let uu____10650 =
            let uu____10659 =
              let uu____10666 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10666) in
            let uu____10671 =
              let uu____10680 =
                let uu____10687 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10687) in
              let uu____10692 =
                let uu____10701 =
                  let uu____10708 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10708) in
                [uu____10701; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10680 :: uu____10692 in
            uu____10659 :: uu____10671 in
          uu____10638 :: uu____10650 in
        uu____10617 :: uu____10629 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10759 =
            FStar_Util.find_map table
              (fun uu____10772  ->
                 match uu____10772 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10789 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10789
                     else FStar_Pervasives_Native.None) in
          (match uu____10759 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10792 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10796 =
      let uu____10797 = FStar_Syntax_Util.un_uinst l in
      uu____10797.FStar_Syntax_Syntax.n in
    match uu____10796 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10801 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10825)::uu____10826 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10837 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10844,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10845))::uu____10846 -> bs
      | uu____10863 ->
          let uu____10864 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10864 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10868 =
                 let uu____10869 = FStar_Syntax_Subst.compress t in
                 uu____10869.FStar_Syntax_Syntax.n in
               (match uu____10868 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10873) ->
                    let uu____10890 =
                      FStar_Util.prefix_until
                        (fun uu___272_10930  ->
                           match uu___272_10930 with
                           | (uu____10937,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10938)) ->
                               false
                           | uu____10941 -> true) bs' in
                    (match uu____10890 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10976,uu____10977) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11049,uu____11050) ->
                         let uu____11123 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11141  ->
                                   match uu____11141 with
                                   | (x,uu____11149) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11123
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11196  ->
                                     match uu____11196 with
                                     | (x,i) ->
                                         let uu____11215 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11215, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11225 -> bs))
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
          let uu____11257 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11257
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
        (let uu____11280 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11280
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11282 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11282))
         else ());
        (let fv =
           let uu____11285 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11285
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
         let uu____11293 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___312_11299 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___312_11299.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___312_11299.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___312_11299.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___312_11299.FStar_Syntax_Syntax.sigattrs)
           }), uu____11293))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___273_11309 =
        match uu___273_11309 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11310 -> false in
      let reducibility uu___274_11314 =
        match uu___274_11314 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11315 -> false in
      let assumption uu___275_11319 =
        match uu___275_11319 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11320 -> false in
      let reification uu___276_11324 =
        match uu___276_11324 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11325 -> true
        | uu____11326 -> false in
      let inferred uu___277_11330 =
        match uu___277_11330 with
        | FStar_Syntax_Syntax.Discriminator uu____11331 -> true
        | FStar_Syntax_Syntax.Projector uu____11332 -> true
        | FStar_Syntax_Syntax.RecordType uu____11337 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11346 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11355 -> false in
      let has_eq uu___278_11359 =
        match uu___278_11359 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11360 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11420 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11425 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11429 =
        let uu____11430 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___279_11434  ->
                  match uu___279_11434 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11435 -> false)) in
        FStar_All.pipe_right uu____11430 Prims.op_Negation in
      if uu____11429
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11448 =
            let uu____11449 =
              let uu____11454 =
                let uu____11455 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11455 msg in
              (uu____11454, r) in
            FStar_Errors.Error uu____11449 in
          FStar_Exn.raise uu____11448 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11463 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11467 =
            let uu____11468 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11468 in
          if uu____11467 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11473),uu____11474) ->
              ((let uu____11490 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11490
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11494 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11494
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11500 ->
              let uu____11509 =
                let uu____11510 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11510 in
              if uu____11509 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11516 ->
              let uu____11523 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11523 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11527 ->
              let uu____11534 =
                let uu____11535 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11535 in
              if uu____11534 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11541 ->
              let uu____11542 =
                let uu____11543 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11543 in
              if uu____11542 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11549 ->
              let uu____11550 =
                let uu____11551 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11551 in
              if uu____11550 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11557 ->
              let uu____11570 =
                let uu____11571 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11571 in
              if uu____11570 then err'1 () else ()
          | uu____11577 -> ()))
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
                          let uu____11640 =
                            let uu____11643 =
                              let uu____11644 =
                                let uu____11651 =
                                  let uu____11652 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11652 in
                                (uu____11651, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11644 in
                            FStar_Syntax_Syntax.mk uu____11643 in
                          uu____11640 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11693  ->
                                  match uu____11693 with
                                  | (x,imp) ->
                                      let uu____11704 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11704, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11706 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11706 in
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
                             let uu____11715 =
                               let uu____11716 =
                                 let uu____11717 =
                                   let uu____11718 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11719 =
                                     let uu____11720 =
                                       let uu____11721 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11721 in
                                     [uu____11720] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11718
                                     uu____11719 in
                                 uu____11717 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11716 in
                             FStar_Syntax_Util.refine x uu____11715 in
                           let uu____11724 =
                             let uu___313_11725 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___313_11725.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___313_11725.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11724) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11740 =
                          FStar_List.map
                            (fun uu____11762  ->
                               match uu____11762 with
                               | (x,uu____11774) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11740 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11823  ->
                                match uu____11823 with
                                | (x,uu____11835) ->
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
                             (let uu____11849 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11849)
                               ||
                               (let uu____11851 =
                                  let uu____11852 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11852.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11851) in
                           let quals =
                             let uu____11856 =
                               let uu____11859 =
                                 let uu____11862 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11862
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11866 =
                                 FStar_List.filter
                                   (fun uu___280_11870  ->
                                      match uu___280_11870 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11871 -> false) iquals in
                               FStar_List.append uu____11859 uu____11866 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11856 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11892 =
                                 let uu____11893 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11893 in
                               FStar_Syntax_Syntax.mk_Total uu____11892 in
                             let uu____11894 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11894 in
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
                           (let uu____11897 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11897
                            then
                              let uu____11898 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11898
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
                                             fun uu____11951  ->
                                               match uu____11951 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11975 =
                                                       let uu____11978 =
                                                         let uu____11979 =
                                                           let uu____11986 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11986,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11979 in
                                                       pos uu____11978 in
                                                     (uu____11975, b)
                                                   else
                                                     (let uu____11990 =
                                                        let uu____11993 =
                                                          let uu____11994 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11994 in
                                                        pos uu____11993 in
                                                      (uu____11990, b)))) in
                                   let pat_true =
                                     let uu____12012 =
                                       let uu____12015 =
                                         let uu____12016 =
                                           let uu____12029 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12029, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12016 in
                                       pos uu____12015 in
                                     (uu____12012,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12063 =
                                       let uu____12066 =
                                         let uu____12067 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12067 in
                                       pos uu____12066 in
                                     (uu____12063,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12079 =
                                     let uu____12082 =
                                       let uu____12083 =
                                         let uu____12106 =
                                           let uu____12109 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12110 =
                                             let uu____12113 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12113] in
                                           uu____12109 :: uu____12110 in
                                         (arg_exp, uu____12106) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12083 in
                                     FStar_Syntax_Syntax.mk uu____12082 in
                                   uu____12079 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12120 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12120
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
                                let uu____12128 =
                                  let uu____12133 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12133 in
                                let uu____12134 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12128;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12134
                                } in
                              let impl =
                                let uu____12138 =
                                  let uu____12139 =
                                    let uu____12146 =
                                      let uu____12149 =
                                        let uu____12150 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12150
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12149] in
                                    ((false, [lb]), uu____12146) in
                                  FStar_Syntax_Syntax.Sig_let uu____12139 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12138;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12168 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12168
                               then
                                 let uu____12169 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12169
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
                                fun uu____12211  ->
                                  match uu____12211 with
                                  | (a,uu____12217) ->
                                      let uu____12218 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12218 with
                                       | (field_name,uu____12224) ->
                                           let field_proj_tm =
                                             let uu____12226 =
                                               let uu____12227 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12227 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12226 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12244 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12276  ->
                                    match uu____12276 with
                                    | (x,uu____12284) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12286 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12286 with
                                         | (field_name,uu____12294) ->
                                             let t =
                                               let uu____12296 =
                                                 let uu____12297 =
                                                   let uu____12300 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12300 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12297 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12296 in
                                             let only_decl =
                                               (let uu____12304 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12304)
                                                 ||
                                                 (let uu____12306 =
                                                    let uu____12307 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12307.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12306) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12321 =
                                                   FStar_List.filter
                                                     (fun uu___281_12325  ->
                                                        match uu___281_12325
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12326 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12321
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___282_12339  ->
                                                         match uu___282_12339
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12340 ->
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
                                             ((let uu____12359 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12359
                                               then
                                                 let uu____12360 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12360
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
                                                           fun uu____12408 
                                                             ->
                                                             match uu____12408
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12432
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12432,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12448
                                                                    =
                                                                    let uu____12451
                                                                    =
                                                                    let uu____12452
                                                                    =
                                                                    let uu____12459
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12459,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12452 in
                                                                    pos
                                                                    uu____12451 in
                                                                    (uu____12448,
                                                                    b))
                                                                   else
                                                                    (let uu____12463
                                                                    =
                                                                    let uu____12466
                                                                    =
                                                                    let uu____12467
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12467 in
                                                                    pos
                                                                    uu____12466 in
                                                                    (uu____12463,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12483 =
                                                     let uu____12486 =
                                                       let uu____12487 =
                                                         let uu____12500 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12500,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12487 in
                                                     pos uu____12486 in
                                                   let uu____12509 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12483,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12509) in
                                                 let body =
                                                   let uu____12521 =
                                                     let uu____12524 =
                                                       let uu____12525 =
                                                         let uu____12548 =
                                                           let uu____12551 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12551] in
                                                         (arg_exp,
                                                           uu____12548) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12525 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12524 in
                                                   uu____12521
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12559 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12559
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
                                                   let uu____12566 =
                                                     let uu____12571 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12571 in
                                                   let uu____12572 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12566;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12572
                                                   } in
                                                 let impl =
                                                   let uu____12576 =
                                                     let uu____12577 =
                                                       let uu____12584 =
                                                         let uu____12587 =
                                                           let uu____12588 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12588
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12587] in
                                                       ((false, [lb]),
                                                         uu____12584) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12577 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12576;
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
                                                 (let uu____12606 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12606
                                                  then
                                                    let uu____12607 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12607
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12244 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12647) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12652 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12652 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12674 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12674 with
                    | (formals,uu____12690) ->
                        let uu____12707 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12739 =
                                   let uu____12740 =
                                     let uu____12741 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12741 in
                                   FStar_Ident.lid_equals typ_lid uu____12740 in
                                 if uu____12739
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12760,uvs',tps,typ0,uu____12764,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12783 -> failwith "Impossible"
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
                        (match uu____12707 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12856 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12856 with
                              | (indices,uu____12872) ->
                                  let refine_domain =
                                    let uu____12890 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___283_12895  ->
                                              match uu___283_12895 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12896 -> true
                                              | uu____12905 -> false)) in
                                    if uu____12890
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___284_12913 =
                                      match uu___284_12913 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12916,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12928 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12929 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12929 with
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
                                    let uu____12940 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12940 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13005  ->
                                               fun uu____13006  ->
                                                 match (uu____13005,
                                                         uu____13006)
                                                 with
                                                 | ((x,uu____13024),(x',uu____13026))
                                                     ->
                                                     let uu____13035 =
                                                       let uu____13042 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13042) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13035) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13043 -> []