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
                                let uu____4939 = subst_c2 "inline all pure" in
                                match uu____4939 with
                                | FStar_Util.Inl (c21,uu____4949) -> c21
                                | FStar_Util.Inr uu____4954 -> c2
                              else c2 in
                            let uu____4960 = lift_and_destruct env c1 c21 in
                            (match uu____4960 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5017 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____5017]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____5019 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____5019] in
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
                                   let uu____5032 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____5033 =
                                     let uu____5036 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____5037 =
                                       let uu____5040 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____5041 =
                                         let uu____5044 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____5045 =
                                           let uu____5048 =
                                             let uu____5049 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____5049 in
                                           [uu____5048] in
                                         uu____5044 :: uu____5045 in
                                       uu____5040 :: uu____5041 in
                                     uu____5036 :: uu____5037 in
                                   uu____5032 :: uu____5033 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____5054 =
                                     let uu____5055 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____5055
                                       wp_args in
                                   uu____5054 FStar_Pervasives_Native.None
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
      | uu____5067 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5086 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5090 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5090
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5097 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5097
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5102 = destruct_comp c1 in
                    match uu____5102 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5118 =
                            let uu____5119 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5120 =
                              let uu____5121 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5122 =
                                let uu____5125 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5126 =
                                  let uu____5129 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5129] in
                                uu____5125 :: uu____5126 in
                              uu____5121 :: uu____5122 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5119
                              uu____5120 in
                          uu____5118 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___298_5132 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___298_5132.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___298_5132.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___298_5132.FStar_Syntax_Syntax.cflags);
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
            let uu____5165 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5165
            then (lc, g0)
            else
              ((let uu____5172 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5172
                then
                  let uu____5173 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5174 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5173 uu____5174
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___267_5184  ->
                          match uu___267_5184 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5187 -> [])) in
                let strengthen uu____5193 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5201 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5201 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5208 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5210 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5210) in
                           if uu____5208
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5217 =
                                 let uu____5218 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5218 in
                               FStar_Syntax_Util.comp_set_flags uu____5217
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5224 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5224
                           then
                             let uu____5225 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5226 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5225 uu____5226
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5229 = destruct_comp c2 in
                           match uu____5229 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5245 =
                                   let uu____5246 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5247 =
                                     let uu____5248 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5249 =
                                       let uu____5252 =
                                         let uu____5253 =
                                           let uu____5254 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5254 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5253 in
                                       let uu____5255 =
                                         let uu____5258 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5258] in
                                       uu____5252 :: uu____5255 in
                                     uu____5248 :: uu____5249 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5246
                                     uu____5247 in
                                 uu____5245 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5262 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5262
                                 then
                                   let uu____5263 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5263
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5266 =
                  let uu___299_5267 = lc in
                  let uu____5268 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5269 =
                    let uu____5272 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5274 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5274) in
                    if uu____5272 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5268;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___299_5267.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5269;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5266,
                  (let uu___300_5279 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___300_5279.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___300_5279.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___300_5279.FStar_TypeChecker_Env.implicits)
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
        let uu____5294 =
          let uu____5299 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5300 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5299, uu____5300) in
        match uu____5294 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5309 =
                let uu____5310 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5311 =
                  let uu____5312 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5313 =
                    let uu____5316 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5316] in
                  uu____5312 :: uu____5313 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5310 uu____5311 in
              uu____5309 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5322 =
                let uu____5323 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5324 =
                  let uu____5325 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5326 =
                    let uu____5329 =
                      let uu____5330 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5330 in
                    let uu____5331 =
                      let uu____5334 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5334] in
                    uu____5329 :: uu____5331 in
                  uu____5325 :: uu____5326 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5323 uu____5324 in
              uu____5322 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5340 =
                let uu____5341 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5342 =
                  let uu____5343 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5344 =
                    let uu____5347 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5348 =
                      let uu____5351 =
                        let uu____5352 =
                          let uu____5353 =
                            let uu____5354 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5354] in
                          FStar_Syntax_Util.abs uu____5353 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5352 in
                      [uu____5351] in
                    uu____5347 :: uu____5348 in
                  uu____5343 :: uu____5344 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5341 uu____5342 in
              uu____5340 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5361 = FStar_TypeChecker_Env.get_range env in
              bind uu____5361 env FStar_Pervasives_Native.None
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
          let comp uu____5380 =
            let uu____5381 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5381
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5384 =
                 let uu____5409 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5410 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5409 uu____5410 in
               match uu____5384 with
               | ((md,uu____5412,uu____5413),(u_res_t,res_t,wp_then),
                  (uu____5417,uu____5418,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5456 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5457 =
                       let uu____5458 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5459 =
                         let uu____5460 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5461 =
                           let uu____5464 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5465 =
                             let uu____5468 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5469 =
                               let uu____5472 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5472] in
                             uu____5468 :: uu____5469 in
                           uu____5464 :: uu____5465 in
                         uu____5460 :: uu____5461 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5458 uu____5459 in
                     uu____5457 FStar_Pervasives_Native.None uu____5456 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5478 =
                     let uu____5479 = FStar_Options.split_cases () in
                     uu____5479 > (Prims.parse_int "0") in
                   if uu____5478
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5485 =
                          let uu____5486 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5487 =
                            let uu____5488 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5489 =
                              let uu____5492 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5492] in
                            uu____5488 :: uu____5489 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5486 uu____5487 in
                        uu____5485 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5495 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5495;
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
      let uu____5502 =
        let uu____5503 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5503 in
      FStar_Syntax_Syntax.fvar uu____5502 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5535  ->
                 match uu____5535 with
                 | (uu____5540,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5545 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5547 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5547
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5567 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5568 =
                 let uu____5569 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5570 =
                   let uu____5571 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5572 =
                     let uu____5575 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5576 =
                       let uu____5579 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5580 =
                         let uu____5583 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5583] in
                       uu____5579 :: uu____5580 in
                     uu____5575 :: uu____5576 in
                   uu____5571 :: uu____5572 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5569 uu____5570 in
               uu____5568 FStar_Pervasives_Native.None uu____5567 in
             let default_case =
               let post_k =
                 let uu____5590 =
                   let uu____5597 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5597] in
                 let uu____5598 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5590 uu____5598 in
               let kwp =
                 let uu____5604 =
                   let uu____5611 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5611] in
                 let uu____5612 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5604 uu____5612 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5617 =
                   let uu____5618 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5618] in
                 let uu____5619 =
                   let uu____5620 =
                     let uu____5623 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5623 in
                   let uu____5624 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5620 uu____5624 in
                 FStar_Syntax_Util.abs uu____5617 uu____5619
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
                 (fun uu____5648  ->
                    fun celse  ->
                      match uu____5648 with
                      | (g,cthen) ->
                          let uu____5656 =
                            let uu____5681 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5681 celse in
                          (match uu____5656 with
                           | ((md,uu____5683,uu____5684),(uu____5685,uu____5686,wp_then),
                              (uu____5688,uu____5689,wp_else)) ->
                               let uu____5709 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5709 []))
                 lcases default_case in
             let uu____5710 =
               let uu____5711 = FStar_Options.split_cases () in
               uu____5711 > (Prims.parse_int "0") in
             if uu____5710
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5715 = destruct_comp comp1 in
                match uu____5715 with
                | (uu____5722,uu____5723,wp) ->
                    let wp1 =
                      let uu____5728 =
                        let uu____5729 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5730 =
                          let uu____5731 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5732 =
                            let uu____5735 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5735] in
                          uu____5731 :: uu____5732 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5729 uu____5730 in
                      uu____5728 FStar_Pervasives_Native.None
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
          let uu____5750 =
            ((let uu____5753 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5753) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5755 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5755) in
          if uu____5750
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5764 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5768 =
            ((let uu____5771 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5771) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5768
          then c
          else
            (let uu____5775 = FStar_Syntax_Util.is_partial_return c in
             if uu____5775
             then c
             else
               (let uu____5779 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5779
                then
                  let uu____5782 =
                    let uu____5783 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5783 in
                  (if uu____5782
                   then
                     let uu____5786 =
                       let uu____5787 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5788 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5787 uu____5788 in
                     failwith uu____5786
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5793 =
                        let uu____5794 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5794 in
                      if uu____5793
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___301_5799 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___301_5799.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___301_5799.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___301_5799.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5810 =
                       let uu____5813 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5813
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5810 in
                   let eq1 =
                     let uu____5817 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5817 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5819 =
                     let uu____5820 =
                       let uu____5825 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5825.FStar_Syntax_Syntax.comp in
                     uu____5820 () in
                   FStar_Syntax_Util.comp_set_flags uu____5819 flags))) in
        let uu____5828 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____5828
        then lc
        else
          (let uu___302_5830 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___302_5830.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___302_5830.FStar_Syntax_Syntax.res_typ);
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
          let uu____5855 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5855 with
          | FStar_Pervasives_Native.None  ->
              let uu____5864 =
                let uu____5865 =
                  let uu____5870 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5871 = FStar_TypeChecker_Env.get_range env in
                  (uu____5870, uu____5871) in
                FStar_Errors.Error uu____5865 in
              FStar_Exn.raise uu____5864
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
            let uu____5904 =
              let uu____5905 = FStar_Syntax_Subst.compress t2 in
              uu____5905.FStar_Syntax_Syntax.n in
            match uu____5904 with
            | FStar_Syntax_Syntax.Tm_type uu____5908 -> true
            | uu____5909 -> false in
          let uu____5910 =
            let uu____5911 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5911.FStar_Syntax_Syntax.n in
          match uu____5910 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5919 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5930 =
                  let uu____5931 =
                    let uu____5932 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5932 in
                  (FStar_Pervasives_Native.None, uu____5931) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5930 in
              let e1 =
                let uu____5942 =
                  let uu____5943 =
                    let uu____5944 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5944] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5943 in
                uu____5942 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5949 -> (e, lc)
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
              (let uu____5978 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5978 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6001 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6023 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6023, false)
            else
              (let uu____6029 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6029, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6040) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6049 =
                  let uu____6050 =
                    let uu____6055 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6055, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6050 in
                FStar_Exn.raise uu____6049
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___303_6065 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___303_6065.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___303_6065.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___303_6065.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6070 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6070 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___304_6078 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___304_6078.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___304_6078.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___304_6078.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___305_6081 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___305_6081.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___305_6081.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___305_6081.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6087 =
                     let uu____6088 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6088
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6093 =
                          let uu____6094 = FStar_Syntax_Subst.compress f1 in
                          uu____6094.FStar_Syntax_Syntax.n in
                        match uu____6093 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6099,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6101;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6102;_},uu____6103)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___306_6125 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___306_6125.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___306_6125.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___306_6125.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6126 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6131 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6131
                              then
                                let uu____6132 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6133 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6134 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6135 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6132 uu____6133 uu____6134 uu____6135
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6138 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6138 with
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
                                  let uu____6151 = destruct_comp ct in
                                  (match uu____6151 with
                                   | (u_t,uu____6161,uu____6162) ->
                                       let wp =
                                         let uu____6166 =
                                           let uu____6167 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6168 =
                                             let uu____6169 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6170 =
                                               let uu____6173 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6173] in
                                             uu____6169 :: uu____6170 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6167 uu____6168 in
                                         uu____6166
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6177 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6177 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6187 =
                                             let uu____6188 =
                                               let uu____6189 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6189] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6188 in
                                           uu____6187
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6193 =
                                         let uu____6198 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6211 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6212 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6198
                                           uu____6211 e cret uu____6212 in
                                       (match uu____6193 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___307_6218 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___307_6218.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___307_6218.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6220 =
                                                let uu____6221 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6221 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6220
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6232 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6232
                                              then
                                                let uu____6233 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6233
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___268_6243  ->
                             match uu___268_6243 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6246 -> [])) in
                   let lc1 =
                     let uu___308_6248 = lc in
                     let uu____6249 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6249;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___309_6251 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___309_6251.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___309_6251.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___309_6251.FStar_TypeChecker_Env.implicits)
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
        let uu____6274 =
          let uu____6275 =
            let uu____6276 =
              let uu____6277 =
                let uu____6278 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6278 in
              [uu____6277] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6276 in
          uu____6275 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6274 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6285 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6285
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6303 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6318 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6347)::(ens,uu____6349)::uu____6350 ->
                    let uu____6379 =
                      let uu____6382 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6382 in
                    let uu____6383 =
                      let uu____6384 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6384 in
                    (uu____6379, uu____6383)
                | uu____6387 ->
                    let uu____6396 =
                      let uu____6397 =
                        let uu____6402 =
                          let uu____6403 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6403 in
                        (uu____6402, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6397 in
                    FStar_Exn.raise uu____6396)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6419)::uu____6420 ->
                    let uu____6439 =
                      let uu____6444 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6444 in
                    (match uu____6439 with
                     | (us_r,uu____6476) ->
                         let uu____6477 =
                           let uu____6482 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6482 in
                         (match uu____6477 with
                          | (us_e,uu____6514) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6517 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6517
                                  us_r in
                              let as_ens =
                                let uu____6519 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6519
                                  us_e in
                              let req =
                                let uu____6523 =
                                  let uu____6524 =
                                    let uu____6525 =
                                      let uu____6536 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6536] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6525 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6524 in
                                uu____6523 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6554 =
                                  let uu____6555 =
                                    let uu____6556 =
                                      let uu____6567 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6567] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6556 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6555 in
                                uu____6554 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6582 =
                                let uu____6585 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6585 in
                              let uu____6586 =
                                let uu____6587 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6587 in
                              (uu____6582, uu____6586)))
                | uu____6590 -> failwith "Impossible"))
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
      (let uu____6616 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6616
       then
         let uu____6617 = FStar_Syntax_Print.term_to_string tm in
         let uu____6618 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6617 uu____6618
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
        (let uu____6636 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6636
         then
           let uu____6637 = FStar_Syntax_Print.term_to_string tm in
           let uu____6638 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6637
             uu____6638
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6643 =
      let uu____6644 =
        let uu____6645 = FStar_Syntax_Subst.compress t in
        uu____6645.FStar_Syntax_Syntax.n in
      match uu____6644 with
      | FStar_Syntax_Syntax.Tm_app uu____6648 -> false
      | uu____6663 -> true in
    if uu____6643
    then t
    else
      (let uu____6665 = FStar_Syntax_Util.head_and_args t in
       match uu____6665 with
       | (head1,args) ->
           let uu____6702 =
             let uu____6703 =
               let uu____6704 = FStar_Syntax_Subst.compress head1 in
               uu____6704.FStar_Syntax_Syntax.n in
             match uu____6703 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6707 -> false in
           if uu____6702
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6729 ->
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
             let uu____6766 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6766 with
             | (formals,uu____6780) ->
                 let n_implicits =
                   let uu____6798 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6874  ->
                             match uu____6874 with
                             | (uu____6881,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6798 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7012 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7012 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7036 =
                     let uu____7037 =
                       let uu____7042 =
                         let uu____7043 = FStar_Util.string_of_int n_expected in
                         let uu____7050 = FStar_Syntax_Print.term_to_string e in
                         let uu____7051 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7043 uu____7050 uu____7051 in
                       let uu____7058 = FStar_TypeChecker_Env.get_range env in
                       (uu____7042, uu____7058) in
                     FStar_Errors.Error uu____7037 in
                   FStar_Exn.raise uu____7036
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___269_7079 =
             match uu___269_7079 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7109 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7109 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7218) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7261,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7294 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7294 with
                           | (v1,uu____7334,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7351 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7351 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7444 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7444)))
                      | (uu____7471,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7517 =
                      let uu____7544 = inst_n_binders t in
                      aux [] uu____7544 bs1 in
                    (match uu____7517 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7615) -> (e, torig, guard)
                          | (uu____7646,[]) when
                              let uu____7677 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7677 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7678 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7710 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7725 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7733 =
      let uu____7736 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7736
        (FStar_List.map
           (fun u  ->
              let uu____7746 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7746 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7733 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7763 = FStar_Util.set_is_empty x in
      if uu____7763
      then []
      else
        (let s =
           let uu____7770 =
             let uu____7773 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7773 in
           FStar_All.pipe_right uu____7770 FStar_Util.set_elements in
         (let uu____7781 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7781
          then
            let uu____7782 =
              let uu____7783 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7783 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7782
          else ());
         (let r =
            let uu____7790 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7790 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7805 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7805
                     then
                       let uu____7806 =
                         let uu____7807 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7807 in
                       let uu____7808 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7809 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7806 uu____7808 uu____7809
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
        let uu____7831 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7831 FStar_Util.fifo_set_elements in
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
        | ([],uu____7863) -> generalized_univ_names
        | (uu____7870,[]) -> explicit_univ_names
        | uu____7877 ->
            let uu____7886 =
              let uu____7887 =
                let uu____7892 =
                  let uu____7893 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7893 in
                (uu____7892, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7887 in
            FStar_Exn.raise uu____7886
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
      (let uu____7910 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7910
       then
         let uu____7911 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7911
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7917 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7917
        then
          let uu____7918 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7918
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
        let uu____7988 =
          let uu____7989 =
            FStar_Util.for_all
              (fun uu____8002  ->
                 match uu____8002 with
                 | (uu____8011,uu____8012,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7989 in
        if uu____7988
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8058 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8058
              then
                let uu____8059 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8059
              else ());
             (let c1 =
                let uu____8062 = FStar_TypeChecker_Env.should_verify env in
                if uu____8062
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
              (let uu____8065 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8065
               then
                 let uu____8066 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8066
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8127 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8127 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8257 =
             match uu____8257 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8323 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8323
                   then
                     let uu____8324 =
                       let uu____8325 =
                         let uu____8328 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8328
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8325
                         (FStar_String.concat ", ") in
                     let uu____8355 =
                       let uu____8356 =
                         let uu____8359 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8359
                           (FStar_List.map
                              (fun uu____8387  ->
                                 match uu____8387 with
                                 | (u,t2) ->
                                     let uu____8394 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8395 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8394 uu____8395)) in
                       FStar_All.pipe_right uu____8356
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8324
                       uu____8355
                   else ());
                  (let univs2 =
                     let uu____8402 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8425  ->
                            match uu____8425 with
                            | (uu____8434,t2) ->
                                let uu____8436 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8436)
                       univs1 uu____8402 in
                   let uvs = gen_uvars uvt in
                   (let uu____8459 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8459
                    then
                      let uu____8460 =
                        let uu____8461 =
                          let uu____8464 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8464
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8461
                          (FStar_String.concat ", ") in
                      let uu____8491 =
                        let uu____8492 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8524  ->
                                  match uu____8524 with
                                  | (u,t2) ->
                                      let uu____8531 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8532 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8531 uu____8532)) in
                        FStar_All.pipe_right uu____8492
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8460
                        uu____8491
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8562 =
             let uu____8595 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8595 in
           match uu____8562 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8713 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8713
                 then ()
                 else
                   (let uu____8715 = lec_hd in
                    match uu____8715 with
                    | (lb1,uu____8723,uu____8724) ->
                        let uu____8725 = lec2 in
                        (match uu____8725 with
                         | (lb2,uu____8733,uu____8734) ->
                             let msg =
                               let uu____8736 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8737 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8736 uu____8737 in
                             let uu____8738 =
                               let uu____8739 =
                                 let uu____8744 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8744) in
                               FStar_Errors.Error uu____8739 in
                             FStar_Exn.raise uu____8738)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8855  ->
                           match uu____8855 with
                           | (u,uu____8863) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8885  ->
                                       match uu____8885 with
                                       | (u',uu____8893) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8898 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8898
                 then ()
                 else
                   (let uu____8900 = lec_hd in
                    match uu____8900 with
                    | (lb1,uu____8908,uu____8909) ->
                        let uu____8910 = lec2 in
                        (match uu____8910 with
                         | (lb2,uu____8918,uu____8919) ->
                             let msg =
                               let uu____8921 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8922 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8921 uu____8922 in
                             let uu____8923 =
                               let uu____8924 =
                                 let uu____8929 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8929) in
                               FStar_Errors.Error uu____8924 in
                             FStar_Exn.raise uu____8923)) in
               let lecs1 =
                 let uu____8939 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8998 = univs_and_uvars_of_lec this_lec in
                        match uu____8998 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8939 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9151 = lec_hd in
                   match uu____9151 with
                   | (lbname,e,c) ->
                       let uu____9161 =
                         let uu____9162 =
                           let uu____9167 =
                             let uu____9168 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9169 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9170 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9168 uu____9169 uu____9170 in
                           let uu____9171 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9167, uu____9171) in
                         FStar_Errors.Error uu____9162 in
                       FStar_Exn.raise uu____9161 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9201  ->
                         match uu____9201 with
                         | (u,k) ->
                             let uu____9214 = FStar_Syntax_Unionfind.find u in
                             (match uu____9214 with
                              | FStar_Pervasives_Native.Some uu____9223 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9230 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9234 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9234 with
                                   | (bs,kres) ->
                                       ((let uu____9272 =
                                           let uu____9273 =
                                             let uu____9276 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9276 in
                                           uu____9273.FStar_Syntax_Syntax.n in
                                         match uu____9272 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9277 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9281 =
                                               let uu____9282 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9282 in
                                             if uu____9281
                                             then fail kres
                                             else ()
                                         | uu____9284 -> fail kres);
                                        (let a =
                                           let uu____9286 =
                                             let uu____9289 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9289 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9286 kres in
                                         let t =
                                           let uu____9293 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9293
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
                      (fun uu____9412  ->
                         match uu____9412 with
                         | (lbname,e,c) ->
                             let uu____9458 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9527 ->
                                   let uu____9542 = (e, c) in
                                   (match uu____9542 with
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
                                                (fun uu____9579  ->
                                                   match uu____9579 with
                                                   | (x,uu____9587) ->
                                                       let uu____9592 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9592)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9602 =
                                                let uu____9603 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9603 in
                                              if uu____9602
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
                                          let uu____9611 =
                                            let uu____9612 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9612.FStar_Syntax_Syntax.n in
                                          match uu____9611 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9635 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9635 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9650 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9652 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9652, gen_tvars)) in
                             (match uu____9458 with
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
        (let uu____9798 = Obj.magic () in ());
        (let uu____9800 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9800
         then
           let uu____9801 =
             let uu____9802 =
               FStar_List.map
                 (fun uu____9815  ->
                    match uu____9815 with
                    | (lb,uu____9823,uu____9824) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9802 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9801
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9845  ->
                match uu____9845 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9874 = gen env is_rec lecs in
           match uu____9874 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9973  ->
                       match uu____9973 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10035 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10035
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10079  ->
                           match uu____10079 with
                           | (l,us,e,c,gvs) ->
                               let uu____10113 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10114 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10115 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10116 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10117 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10113 uu____10114 uu____10115
                                 uu____10116 uu____10117))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10158  ->
                match uu____10158 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10202 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10202, t, c, gvs)) univnames_lecs
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
              (let uu____10245 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10245 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10251 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10251) in
          let is_var e1 =
            let uu____10258 =
              let uu____10259 = FStar_Syntax_Subst.compress e1 in
              uu____10259.FStar_Syntax_Syntax.n in
            match uu____10258 with
            | FStar_Syntax_Syntax.Tm_name uu____10262 -> true
            | uu____10263 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___310_10279 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___310_10279.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___310_10279.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10280 -> e2 in
          let env2 =
            let uu___311_10282 = env1 in
            let uu____10283 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___311_10282.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___311_10282.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___311_10282.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___311_10282.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___311_10282.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___311_10282.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___311_10282.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___311_10282.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___311_10282.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___311_10282.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___311_10282.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___311_10282.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___311_10282.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___311_10282.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___311_10282.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10283;
              FStar_TypeChecker_Env.is_iface =
                (uu___311_10282.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___311_10282.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___311_10282.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___311_10282.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___311_10282.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___311_10282.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___311_10282.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___311_10282.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___311_10282.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___311_10282.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___311_10282.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___311_10282.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___311_10282.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___311_10282.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___311_10282.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___311_10282.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___311_10282.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___311_10282.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10284 = check env2 t1 t2 in
          match uu____10284 with
          | FStar_Pervasives_Native.None  ->
              let uu____10291 =
                let uu____10292 =
                  let uu____10297 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10298 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10297, uu____10298) in
                FStar_Errors.Error uu____10292 in
              FStar_Exn.raise uu____10291
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10305 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10305
                then
                  let uu____10306 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10306
                else ());
               (let uu____10308 = decorate e t2 in (uu____10308, g)))
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
        let uu____10336 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10336
        then
          let uu____10341 = discharge g1 in
          let uu____10342 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10341, uu____10342)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10355 =
               let uu____10356 =
                 let uu____10357 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10357 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10356
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10355
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10359 = destruct_comp c1 in
           match uu____10359 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10376 = FStar_TypeChecker_Env.get_range env in
                 let uu____10377 =
                   let uu____10378 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10379 =
                     let uu____10380 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10381 =
                       let uu____10384 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10384] in
                     uu____10380 :: uu____10381 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10378 uu____10379 in
                 uu____10377 FStar_Pervasives_Native.None uu____10376 in
               ((let uu____10388 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10388
                 then
                   let uu____10389 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10389
                 else ());
                (let g2 =
                   let uu____10392 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10392 in
                 let uu____10393 = discharge g2 in
                 let uu____10394 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10393, uu____10394))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___270_10418 =
        match uu___270_10418 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10426)::[] -> f fst1
        | uu____10443 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10448 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10448
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10457 =
          let uu____10460 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10460 in
        FStar_All.pipe_right uu____10457
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10471 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10471
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___271_10485 =
        match uu___271_10485 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10493)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10512)::[] ->
            let uu____10541 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10541
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10546 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10556 =
          let uu____10563 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10563) in
        let uu____10568 =
          let uu____10577 =
            let uu____10584 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10584) in
          let uu____10589 =
            let uu____10598 =
              let uu____10605 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10605) in
            let uu____10610 =
              let uu____10619 =
                let uu____10626 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10626) in
              let uu____10631 =
                let uu____10640 =
                  let uu____10647 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10647) in
                [uu____10640; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10619 :: uu____10631 in
            uu____10598 :: uu____10610 in
          uu____10577 :: uu____10589 in
        uu____10556 :: uu____10568 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10698 =
            FStar_Util.find_map table
              (fun uu____10711  ->
                 match uu____10711 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10728 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10728
                     else FStar_Pervasives_Native.None) in
          (match uu____10698 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10731 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10735 =
      let uu____10736 = FStar_Syntax_Util.un_uinst l in
      uu____10736.FStar_Syntax_Syntax.n in
    match uu____10735 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10740 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10764)::uu____10765 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10776 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10783,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10784))::uu____10785 -> bs
      | uu____10802 ->
          let uu____10803 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10803 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10807 =
                 let uu____10808 = FStar_Syntax_Subst.compress t in
                 uu____10808.FStar_Syntax_Syntax.n in
               (match uu____10807 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10812) ->
                    let uu____10829 =
                      FStar_Util.prefix_until
                        (fun uu___272_10869  ->
                           match uu___272_10869 with
                           | (uu____10876,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10877)) ->
                               false
                           | uu____10880 -> true) bs' in
                    (match uu____10829 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10915,uu____10916) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10988,uu____10989) ->
                         let uu____11062 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11080  ->
                                   match uu____11080 with
                                   | (x,uu____11088) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11062
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11135  ->
                                     match uu____11135 with
                                     | (x,i) ->
                                         let uu____11154 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11154, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11164 -> bs))
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
          let uu____11196 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11196
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
        (let uu____11219 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11219
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11221 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11221))
         else ());
        (let fv =
           let uu____11224 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11224
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
         let uu____11232 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___312_11238 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___312_11238.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___312_11238.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___312_11238.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___312_11238.FStar_Syntax_Syntax.sigattrs)
           }), uu____11232))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___273_11248 =
        match uu___273_11248 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11249 -> false in
      let reducibility uu___274_11253 =
        match uu___274_11253 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11254 -> false in
      let assumption uu___275_11258 =
        match uu___275_11258 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11259 -> false in
      let reification uu___276_11263 =
        match uu___276_11263 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11264 -> true
        | uu____11265 -> false in
      let inferred uu___277_11269 =
        match uu___277_11269 with
        | FStar_Syntax_Syntax.Discriminator uu____11270 -> true
        | FStar_Syntax_Syntax.Projector uu____11271 -> true
        | FStar_Syntax_Syntax.RecordType uu____11276 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11285 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11294 -> false in
      let has_eq uu___278_11298 =
        match uu___278_11298 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11299 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11359 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11364 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11368 =
        let uu____11369 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___279_11373  ->
                  match uu___279_11373 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11374 -> false)) in
        FStar_All.pipe_right uu____11369 Prims.op_Negation in
      if uu____11368
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11387 =
            let uu____11388 =
              let uu____11393 =
                let uu____11394 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11394 msg in
              (uu____11393, r) in
            FStar_Errors.Error uu____11388 in
          FStar_Exn.raise uu____11387 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11402 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11406 =
            let uu____11407 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11407 in
          if uu____11406 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11412),uu____11413) ->
              ((let uu____11429 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11429
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11433 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11433
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11439 ->
              let uu____11448 =
                let uu____11449 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11449 in
              if uu____11448 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11455 ->
              let uu____11462 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11462 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11466 ->
              let uu____11473 =
                let uu____11474 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11474 in
              if uu____11473 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11480 ->
              let uu____11481 =
                let uu____11482 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11482 in
              if uu____11481 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11488 ->
              let uu____11489 =
                let uu____11490 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11490 in
              if uu____11489 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11496 ->
              let uu____11509 =
                let uu____11510 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11510 in
              if uu____11509 then err'1 () else ()
          | uu____11516 -> ()))
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
                          let uu____11579 =
                            let uu____11582 =
                              let uu____11583 =
                                let uu____11590 =
                                  let uu____11591 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11591 in
                                (uu____11590, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11583 in
                            FStar_Syntax_Syntax.mk uu____11582 in
                          uu____11579 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11632  ->
                                  match uu____11632 with
                                  | (x,imp) ->
                                      let uu____11643 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11643, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11645 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11645 in
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
                             let uu____11654 =
                               let uu____11655 =
                                 let uu____11656 =
                                   let uu____11657 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11658 =
                                     let uu____11659 =
                                       let uu____11660 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11660 in
                                     [uu____11659] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11657
                                     uu____11658 in
                                 uu____11656 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11655 in
                             FStar_Syntax_Util.refine x uu____11654 in
                           let uu____11663 =
                             let uu___313_11664 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___313_11664.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___313_11664.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11663) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11679 =
                          FStar_List.map
                            (fun uu____11701  ->
                               match uu____11701 with
                               | (x,uu____11713) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11679 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11762  ->
                                match uu____11762 with
                                | (x,uu____11774) ->
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
                             (let uu____11788 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11788)
                               ||
                               (let uu____11790 =
                                  let uu____11791 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11791.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11790) in
                           let quals =
                             let uu____11795 =
                               let uu____11798 =
                                 let uu____11801 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11801
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11805 =
                                 FStar_List.filter
                                   (fun uu___280_11809  ->
                                      match uu___280_11809 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11810 -> false) iquals in
                               FStar_List.append uu____11798 uu____11805 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11795 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11831 =
                                 let uu____11832 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11832 in
                               FStar_Syntax_Syntax.mk_Total uu____11831 in
                             let uu____11833 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11833 in
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
                           (let uu____11836 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11836
                            then
                              let uu____11837 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11837
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
                                             fun uu____11890  ->
                                               match uu____11890 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11914 =
                                                       let uu____11917 =
                                                         let uu____11918 =
                                                           let uu____11925 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11925,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11918 in
                                                       pos uu____11917 in
                                                     (uu____11914, b)
                                                   else
                                                     (let uu____11929 =
                                                        let uu____11932 =
                                                          let uu____11933 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11933 in
                                                        pos uu____11932 in
                                                      (uu____11929, b)))) in
                                   let pat_true =
                                     let uu____11951 =
                                       let uu____11954 =
                                         let uu____11955 =
                                           let uu____11968 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11968, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11955 in
                                       pos uu____11954 in
                                     (uu____11951,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12002 =
                                       let uu____12005 =
                                         let uu____12006 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12006 in
                                       pos uu____12005 in
                                     (uu____12002,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12018 =
                                     let uu____12021 =
                                       let uu____12022 =
                                         let uu____12045 =
                                           let uu____12048 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12049 =
                                             let uu____12052 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12052] in
                                           uu____12048 :: uu____12049 in
                                         (arg_exp, uu____12045) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12022 in
                                     FStar_Syntax_Syntax.mk uu____12021 in
                                   uu____12018 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12059 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12059
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
                                let uu____12067 =
                                  let uu____12072 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12072 in
                                let uu____12073 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12067;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12073
                                } in
                              let impl =
                                let uu____12077 =
                                  let uu____12078 =
                                    let uu____12085 =
                                      let uu____12088 =
                                        let uu____12089 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12089
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12088] in
                                    ((false, [lb]), uu____12085) in
                                  FStar_Syntax_Syntax.Sig_let uu____12078 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12077;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12107 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12107
                               then
                                 let uu____12108 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12108
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
                                fun uu____12150  ->
                                  match uu____12150 with
                                  | (a,uu____12156) ->
                                      let uu____12157 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12157 with
                                       | (field_name,uu____12163) ->
                                           let field_proj_tm =
                                             let uu____12165 =
                                               let uu____12166 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12166 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12165 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12183 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12215  ->
                                    match uu____12215 with
                                    | (x,uu____12223) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12225 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12225 with
                                         | (field_name,uu____12233) ->
                                             let t =
                                               let uu____12235 =
                                                 let uu____12236 =
                                                   let uu____12239 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12239 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12236 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12235 in
                                             let only_decl =
                                               (let uu____12243 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12243)
                                                 ||
                                                 (let uu____12245 =
                                                    let uu____12246 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12246.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12245) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12260 =
                                                   FStar_List.filter
                                                     (fun uu___281_12264  ->
                                                        match uu___281_12264
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12265 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12260
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___282_12278  ->
                                                         match uu___282_12278
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12279 ->
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
                                             ((let uu____12298 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12298
                                               then
                                                 let uu____12299 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12299
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
                                                           fun uu____12347 
                                                             ->
                                                             match uu____12347
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12371
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12371,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12387
                                                                    =
                                                                    let uu____12390
                                                                    =
                                                                    let uu____12391
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12398,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12391 in
                                                                    pos
                                                                    uu____12390 in
                                                                    (uu____12387,
                                                                    b))
                                                                   else
                                                                    (let uu____12402
                                                                    =
                                                                    let uu____12405
                                                                    =
                                                                    let uu____12406
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12406 in
                                                                    pos
                                                                    uu____12405 in
                                                                    (uu____12402,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12422 =
                                                     let uu____12425 =
                                                       let uu____12426 =
                                                         let uu____12439 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12439,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12426 in
                                                     pos uu____12425 in
                                                   let uu____12448 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12422,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12448) in
                                                 let body =
                                                   let uu____12460 =
                                                     let uu____12463 =
                                                       let uu____12464 =
                                                         let uu____12487 =
                                                           let uu____12490 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12490] in
                                                         (arg_exp,
                                                           uu____12487) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12464 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12463 in
                                                   uu____12460
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12498 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12498
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
                                                   let uu____12505 =
                                                     let uu____12510 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12510 in
                                                   let uu____12511 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12505;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12511
                                                   } in
                                                 let impl =
                                                   let uu____12515 =
                                                     let uu____12516 =
                                                       let uu____12523 =
                                                         let uu____12526 =
                                                           let uu____12527 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12527
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12526] in
                                                       ((false, [lb]),
                                                         uu____12523) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12516 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12515;
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
                                                 (let uu____12545 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12545
                                                  then
                                                    let uu____12546 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12546
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12183 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12586) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12591 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12591 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12613 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12613 with
                    | (formals,uu____12629) ->
                        let uu____12646 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12678 =
                                   let uu____12679 =
                                     let uu____12680 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12680 in
                                   FStar_Ident.lid_equals typ_lid uu____12679 in
                                 if uu____12678
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12699,uvs',tps,typ0,uu____12703,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12722 -> failwith "Impossible"
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
                        (match uu____12646 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12795 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12795 with
                              | (indices,uu____12811) ->
                                  let refine_domain =
                                    let uu____12829 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___283_12834  ->
                                              match uu___283_12834 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12835 -> true
                                              | uu____12844 -> false)) in
                                    if uu____12829
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___284_12852 =
                                      match uu___284_12852 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12855,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12867 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12868 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12868 with
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
                                    let uu____12879 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12879 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12944  ->
                                               fun uu____12945  ->
                                                 match (uu____12944,
                                                         uu____12945)
                                                 with
                                                 | ((x,uu____12963),(x',uu____12965))
                                                     ->
                                                     let uu____12974 =
                                                       let uu____12981 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12981) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12974) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12982 -> []