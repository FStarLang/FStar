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
  fun uu___268_89  ->
    match uu___268_89 with
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
                     let uu___289_253 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____254 =
                       let uu____269 =
                         let uu____282 = as_uvar u in
                         (reason, env, uu____282, t, k, r) in
                       [uu____269] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___289_253.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___289_253.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___289_253.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___290_488 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___290_488.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___290_488.FStar_Syntax_Syntax.index);
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
                ((let uu___291_1118 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___291_1118.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___291_1118.FStar_Syntax_Syntax.index);
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
                       let uu___292_1229 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___292_1229.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___292_1229.FStar_Syntax_Syntax.index);
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
                            let uu___293_1261 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___293_1261.FStar_Syntax_Syntax.p)
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
                       (let uu___294_1983 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___294_1983.FStar_Syntax_Syntax.p)
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
                          let uu___295_2567 = p1 in
                          let uu____2570 =
                            let uu____2571 =
                              let uu____2584 = aux f pats1 in
                              (fv, uu____2584) in
                            FStar_Syntax_Syntax.Pat_cons uu____2571 in
                          {
                            FStar_Syntax_Syntax.v = uu____2570;
                            FStar_Syntax_Syntax.p =
                              (uu___295_2567.FStar_Syntax_Syntax.p)
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
                  let uu___296_2855 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___296_2855.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___296_2855.FStar_Syntax_Syntax.index);
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
                  let uu___297_2866 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___297_2866.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___297_2866.FStar_Syntax_Syntax.index);
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
      let uu___298_4278 = lc in
      let uu____4279 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___298_4278.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4279;
        FStar_Syntax_Syntax.cflags =
          (uu___298_4278.FStar_Syntax_Syntax.cflags);
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
            let uu___299_4358 = g in
            let uu____4359 =
              let uu____4360 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4360 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4359;
              FStar_TypeChecker_Env.deferred =
                (uu___299_4358.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___299_4358.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___299_4358.FStar_TypeChecker_Env.implicits)
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
        let uu___300_4471 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___300_4471.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___300_4471.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___300_4471.FStar_Syntax_Syntax.cflags);
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
                                           let uu___301_4879 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___301_4879.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___301_4879.FStar_Syntax_Syntax.index);
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
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____4938 = destruct_comp c1_typ in
                            (match uu____4938 with
                             | (u_res_t1,res_t1,uu____4947) ->
                                 let should_inline_c1 uu____4951 =
                                   ((FStar_Syntax_Util.is_pure_or_ghost_comp
                                       c1)
                                      &&
                                      (let uu____4953 =
                                         FStar_Syntax_Util.is_unit res_t1 in
                                       Prims.op_Negation uu____4953))
                                     &&
                                     (match e1opt with
                                      | FStar_Pervasives_Native.Some e1 ->
                                          let uu____4965 =
                                            FStar_Syntax_Util.head_and_args'
                                              e1 in
                                          (match uu____4965 with
                                           | (head1,uu____4979) ->
                                               let uu____4996 =
                                                 let uu____4997 =
                                                   FStar_Syntax_Util.un_uinst
                                                     head1 in
                                                 uu____4997.FStar_Syntax_Syntax.n in
                                               (match uu____4996 with
                                                | FStar_Syntax_Syntax.Tm_fvar
                                                    fv ->
                                                    let uu____5001 =
                                                      let uu____5022 =
                                                        FStar_Syntax_Syntax.lid_of_fv
                                                          fv in
                                                      FStar_TypeChecker_Env.lookup_qname
                                                        env uu____5022 in
                                                    (match uu____5001 with
                                                     | FStar_Pervasives_Native.Some
                                                         (FStar_Util.Inr
                                                          (se,uu____5024),uu____5025)
                                                         ->
                                                         Prims.op_Negation
                                                           (FStar_List.existsb
                                                              (fun
                                                                 uu___269_5073
                                                                  ->
                                                                 match uu___269_5073
                                                                 with
                                                                 | FStar_Syntax_Syntax.Irreducible
                                                                     -> true
                                                                 | FStar_Syntax_Syntax.Assumption
                                                                     -> true
                                                                 | uu____5074
                                                                    -> false)
                                                              se.FStar_Syntax_Syntax.sigquals)
                                                     | uu____5075 -> true)
                                                | FStar_Syntax_Syntax.Tm_let
                                                    ((true ,uu____5096),uu____5097)
                                                    -> false
                                                | uu____5112 -> true))
                                      | uu____5113 -> false) in
                                 let c21 =
                                   let uu____5117 = should_inline_c1 () in
                                   if uu____5117
                                   then
                                     match (e1opt, b) with
                                     | (FStar_Pervasives_Native.Some
                                        e,FStar_Pervasives_Native.Some bv) ->
                                         let uu____5128 =
                                           subst_c2 "inline all pure" in
                                         (match uu____5128 with
                                          | FStar_Util.Inl (c21,uu____5138)
                                              ->
                                              let c2_typ =
                                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                                  env c21 in
                                              let uu____5144 =
                                                destruct_comp c2_typ in
                                              (match uu____5144 with
                                               | (u_res_t,res_t,wp) ->
                                                   let md =
                                                     FStar_TypeChecker_Env.get_effect_decl
                                                       env
                                                       c2_typ.FStar_Syntax_Syntax.effect_name in
                                                   let wp1 =
                                                     if
                                                       FStar_List.existsb
                                                         (fun uu___270_5161 
                                                            ->
                                                            match uu___270_5161
                                                            with
                                                            | FStar_Syntax_Syntax.RETURN
                                                                 -> true
                                                            | FStar_Syntax_Syntax.PARTIAL_RETURN
                                                                 -> true
                                                            | uu____5162 ->
                                                                false)
                                                         c1_typ.FStar_Syntax_Syntax.flags
                                                     then
                                                       let uu____5163 =
                                                         let uu____5164 =
                                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                                             [u_res_t] env md
                                                             md.FStar_Syntax_Syntax.assume_p in
                                                         let uu____5165 =
                                                           let uu____5166 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               res_t in
                                                           let uu____5167 =
                                                             let uu____5170 =
                                                               let uu____5171
                                                                 =
                                                                 let uu____5172
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    bv in
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   u_res_t1
                                                                   res_t1
                                                                   uu____5172
                                                                   e in
                                                               FStar_Syntax_Syntax.as_arg
                                                                 uu____5171 in
                                                             let uu____5173 =
                                                               let uu____5176
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   wp in
                                                               [uu____5176] in
                                                             uu____5170 ::
                                                               uu____5173 in
                                                           uu____5166 ::
                                                             uu____5167 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____5164
                                                           uu____5165 in
                                                       uu____5163
                                                         FStar_Pervasives_Native.None
                                                         wp.FStar_Syntax_Syntax.pos
                                                     else wp in
                                                   mk_comp md u_res_t res_t
                                                     wp1
                                                     c2_typ.FStar_Syntax_Syntax.flags)
                                          | FStar_Util.Inr uu____5180 -> c2)
                                     | (uu____5185,uu____5186) -> c2
                                   else c2 in
                                 let uu____5196 =
                                   lift_and_destruct env c1 c21 in
                                 (match uu____5196 with
                                  | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                      ->
                                      let bs =
                                        match b with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5253 =
                                              FStar_Syntax_Syntax.null_binder
                                                t1 in
                                            [uu____5253]
                                        | FStar_Pervasives_Native.Some x ->
                                            let uu____5255 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____5255] in
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
                                        let uu____5268 =
                                          FStar_Syntax_Syntax.as_arg r11 in
                                        let uu____5269 =
                                          let uu____5272 =
                                            FStar_Syntax_Syntax.as_arg t1 in
                                          let uu____5273 =
                                            let uu____5276 =
                                              FStar_Syntax_Syntax.as_arg t2 in
                                            let uu____5277 =
                                              let uu____5280 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wp1 in
                                              let uu____5281 =
                                                let uu____5284 =
                                                  let uu____5285 = mk_lam wp2 in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____5285 in
                                                [uu____5284] in
                                              uu____5280 :: uu____5281 in
                                            uu____5276 :: uu____5277 in
                                          uu____5272 :: uu____5273 in
                                        uu____5268 :: uu____5269 in
                                      let wp =
                                        let uu____5289 =
                                          let uu____5290 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t1; u_t2] env md
                                              md.FStar_Syntax_Syntax.bind_wp in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____5290 wp_args in
                                        uu____5289
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      mk_comp md u_t2 t2 wp [])))) in
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
      | uu____5302 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5321 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5325 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5325
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5332 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5332
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5337 = destruct_comp c1 in
                    match uu____5337 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5353 =
                            let uu____5354 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5355 =
                              let uu____5356 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5357 =
                                let uu____5360 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5361 =
                                  let uu____5364 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5364] in
                                uu____5360 :: uu____5361 in
                              uu____5356 :: uu____5357 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5354
                              uu____5355 in
                          uu____5353 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___302_5367 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___302_5367.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___302_5367.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___302_5367.FStar_Syntax_Syntax.cflags);
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
            let uu____5400 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5400
            then (lc, g0)
            else
              ((let uu____5407 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5407
                then
                  let uu____5408 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5409 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5408 uu____5409
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___271_5419  ->
                          match uu___271_5419 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5422 -> [])) in
                let strengthen uu____5428 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5436 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5436 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         ((let uu____5441 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5441
                           then
                             let uu____5442 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5443 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5442 uu____5443
                           else ());
                          (let c1 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                           let uu____5446 = destruct_comp c1 in
                           match uu____5446 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c1.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5462 =
                                   let uu____5463 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5464 =
                                     let uu____5465 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5466 =
                                       let uu____5469 =
                                         let uu____5470 =
                                           let uu____5471 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5471 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5470 in
                                       let uu____5472 =
                                         let uu____5475 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5475] in
                                       uu____5469 :: uu____5472 in
                                     uu____5465 :: uu____5466 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5463
                                     uu____5464 in
                                 uu____5462 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5479 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5479
                                 then
                                   let uu____5480 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5480
                                 else ());
                                (let c2 = mk_comp md u_res_t res_t wp1 flags in
                                 c2))))) in
                let uu____5483 =
                  let uu___303_5484 = lc in
                  let uu____5485 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5486 =
                    let uu____5489 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5491 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5491) in
                    if uu____5489 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5485;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___303_5484.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5486;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5483,
                  (let uu___304_5496 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___304_5496.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___304_5496.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___304_5496.FStar_TypeChecker_Env.implicits)
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
        let uu____5511 =
          let uu____5516 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5517 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5516, uu____5517) in
        match uu____5511 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5526 =
                let uu____5527 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5528 =
                  let uu____5529 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5530 =
                    let uu____5533 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5533] in
                  uu____5529 :: uu____5530 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5527 uu____5528 in
              uu____5526 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5539 =
                let uu____5540 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5541 =
                  let uu____5542 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5543 =
                    let uu____5546 =
                      let uu____5547 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5547 in
                    let uu____5548 =
                      let uu____5551 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5551] in
                    uu____5546 :: uu____5548 in
                  uu____5542 :: uu____5543 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5540 uu____5541 in
              uu____5539 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5557 =
                let uu____5558 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5559 =
                  let uu____5560 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5561 =
                    let uu____5564 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5565 =
                      let uu____5568 =
                        let uu____5569 =
                          let uu____5570 =
                            let uu____5571 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5571] in
                          FStar_Syntax_Util.abs uu____5570 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5569 in
                      [uu____5568] in
                    uu____5564 :: uu____5565 in
                  uu____5560 :: uu____5561 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5558 uu____5559 in
              uu____5557 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5578 = FStar_TypeChecker_Env.get_range env in
              bind uu____5578 env FStar_Pervasives_Native.None
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
          let comp uu____5597 =
            let uu____5598 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5598
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5601 =
                 let uu____5626 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5627 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5626 uu____5627 in
               match uu____5601 with
               | ((md,uu____5629,uu____5630),(u_res_t,res_t,wp_then),
                  (uu____5634,uu____5635,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5673 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5674 =
                       let uu____5675 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5676 =
                         let uu____5677 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5678 =
                           let uu____5681 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5682 =
                             let uu____5685 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5686 =
                               let uu____5689 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5689] in
                             uu____5685 :: uu____5686 in
                           uu____5681 :: uu____5682 in
                         uu____5677 :: uu____5678 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5675 uu____5676 in
                     uu____5674 FStar_Pervasives_Native.None uu____5673 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5695 =
                     let uu____5696 = FStar_Options.split_cases () in
                     uu____5696 > (Prims.parse_int "0") in
                   if uu____5695
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5702 =
                          let uu____5703 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5704 =
                            let uu____5705 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5706 =
                              let uu____5709 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5709] in
                            uu____5705 :: uu____5706 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5703 uu____5704 in
                        uu____5702 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5712 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5712;
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
      let uu____5719 =
        let uu____5720 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5720 in
      FStar_Syntax_Syntax.fvar uu____5719 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5752  ->
                 match uu____5752 with
                 | (uu____5757,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5762 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5764 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5764
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5784 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5785 =
                 let uu____5786 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5787 =
                   let uu____5788 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5789 =
                     let uu____5792 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5793 =
                       let uu____5796 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5797 =
                         let uu____5800 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5800] in
                       uu____5796 :: uu____5797 in
                     uu____5792 :: uu____5793 in
                   uu____5788 :: uu____5789 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5786 uu____5787 in
               uu____5785 FStar_Pervasives_Native.None uu____5784 in
             let default_case =
               let post_k =
                 let uu____5807 =
                   let uu____5814 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5814] in
                 let uu____5815 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5807 uu____5815 in
               let kwp =
                 let uu____5821 =
                   let uu____5828 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5828] in
                 let uu____5829 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5821 uu____5829 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5834 =
                   let uu____5835 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5835] in
                 let uu____5836 =
                   let uu____5837 =
                     let uu____5840 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5840 in
                   let uu____5841 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5837 uu____5841 in
                 FStar_Syntax_Util.abs uu____5834 uu____5836
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
                 (fun uu____5865  ->
                    fun celse  ->
                      match uu____5865 with
                      | (g,cthen) ->
                          let uu____5873 =
                            let uu____5898 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5898 celse in
                          (match uu____5873 with
                           | ((md,uu____5900,uu____5901),(uu____5902,uu____5903,wp_then),
                              (uu____5905,uu____5906,wp_else)) ->
                               let uu____5926 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5926 []))
                 lcases default_case in
             let uu____5927 =
               let uu____5928 = FStar_Options.split_cases () in
               uu____5928 > (Prims.parse_int "0") in
             if uu____5927
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5932 = destruct_comp comp1 in
                match uu____5932 with
                | (uu____5939,uu____5940,wp) ->
                    let wp1 =
                      let uu____5945 =
                        let uu____5946 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5947 =
                          let uu____5948 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5949 =
                            let uu____5952 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5952] in
                          uu____5948 :: uu____5949 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5946 uu____5947 in
                      uu____5945 FStar_Pervasives_Native.None
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
          let uu____5967 =
            ((let uu____5970 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5970) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5972 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5972) in
          if uu____5967
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5981 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5985 =
            ((let uu____5988 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5988) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5985
          then c
          else
            (let uu____5992 = FStar_Syntax_Util.is_partial_return c in
             if uu____5992
             then c
             else
               (let uu____5996 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5996
                then
                  let uu____5999 =
                    let uu____6000 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____6000 in
                  (if uu____5999
                   then
                     let uu____6003 =
                       let uu____6004 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____6005 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____6004 uu____6005 in
                     failwith uu____6003
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____6010 =
                        let uu____6011 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____6011 in
                      if uu____6010
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___305_6016 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___305_6016.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___305_6016.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___305_6016.FStar_Syntax_Syntax.effect_args);
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
                     let uu____6027 =
                       let uu____6030 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____6030
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____6027 in
                   let eq1 =
                     let uu____6034 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____6034 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____6036 =
                     let uu____6037 =
                       let uu____6042 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____6042.FStar_Syntax_Syntax.comp in
                     uu____6037 () in
                   FStar_Syntax_Util.comp_set_flags uu____6036 flags))) in
        let uu____6045 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____6045
        then lc
        else
          (let uu___306_6047 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___306_6047.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___306_6047.FStar_Syntax_Syntax.res_typ);
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
          let uu____6072 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6072 with
          | FStar_Pervasives_Native.None  ->
              let uu____6081 =
                let uu____6082 =
                  let uu____6087 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____6088 = FStar_TypeChecker_Env.get_range env in
                  (uu____6087, uu____6088) in
                FStar_Errors.Error uu____6082 in
              FStar_Exn.raise uu____6081
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
            let uu____6121 =
              let uu____6122 = FStar_Syntax_Subst.compress t2 in
              uu____6122.FStar_Syntax_Syntax.n in
            match uu____6121 with
            | FStar_Syntax_Syntax.Tm_type uu____6125 -> true
            | uu____6126 -> false in
          let uu____6127 =
            let uu____6128 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6128.FStar_Syntax_Syntax.n in
          match uu____6127 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6136 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6147 =
                  let uu____6148 =
                    let uu____6149 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6149 in
                  (FStar_Pervasives_Native.None, uu____6148) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6147 in
              let e1 =
                let uu____6159 =
                  let uu____6160 =
                    let uu____6161 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6161] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6160 in
                uu____6159 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6166 -> (e, lc)
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
              (let uu____6195 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6195 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6218 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6240 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6240, false)
            else
              (let uu____6246 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6246, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6257) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6266 =
                  let uu____6267 =
                    let uu____6272 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6272, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6267 in
                FStar_Exn.raise uu____6266
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___307_6282 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___307_6282.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___307_6282.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___307_6282.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6287 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6287 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___308_6295 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___308_6295.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___308_6295.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___308_6295.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___309_6298 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___309_6298.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___309_6298.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___309_6298.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6304 =
                     let uu____6305 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6305
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6310 =
                          let uu____6311 = FStar_Syntax_Subst.compress f1 in
                          uu____6311.FStar_Syntax_Syntax.n in
                        match uu____6310 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6316,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6318;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6319;_},uu____6320)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___310_6342 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___310_6342.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___310_6342.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___310_6342.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6343 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6348 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6348
                              then
                                let uu____6349 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6350 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6351 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6352 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6349 uu____6350 uu____6351 uu____6352
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6355 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6355 with
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
                                  let uu____6368 = destruct_comp ct in
                                  (match uu____6368 with
                                   | (u_t,uu____6378,uu____6379) ->
                                       let wp =
                                         let uu____6383 =
                                           let uu____6384 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6385 =
                                             let uu____6386 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6387 =
                                               let uu____6390 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6390] in
                                             uu____6386 :: uu____6387 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6384 uu____6385 in
                                         uu____6383
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6394 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6394 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6404 =
                                             let uu____6405 =
                                               let uu____6406 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6406] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6405 in
                                           uu____6404
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6410 =
                                         let uu____6415 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6428 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6429 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6415
                                           uu____6428 e cret uu____6429 in
                                       (match uu____6410 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___311_6435 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___311_6435.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___311_6435.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6437 =
                                                let uu____6438 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6438 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6437
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6449 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6449
                                              then
                                                let uu____6450 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6450
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___272_6460  ->
                             match uu___272_6460 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6463 -> [])) in
                   let lc1 =
                     let uu___312_6465 = lc in
                     let uu____6466 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6466;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___313_6468 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___313_6468.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___313_6468.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___313_6468.FStar_TypeChecker_Env.implicits)
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
        let uu____6491 =
          let uu____6492 =
            let uu____6493 =
              let uu____6494 =
                let uu____6495 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6495 in
              [uu____6494] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6493 in
          uu____6492 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6491 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6502 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6502
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6520 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6535 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6564)::(ens,uu____6566)::uu____6567 ->
                    let uu____6596 =
                      let uu____6599 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6599 in
                    let uu____6600 =
                      let uu____6601 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6601 in
                    (uu____6596, uu____6600)
                | uu____6604 ->
                    let uu____6613 =
                      let uu____6614 =
                        let uu____6619 =
                          let uu____6620 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6620 in
                        (uu____6619, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6614 in
                    FStar_Exn.raise uu____6613)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6636)::uu____6637 ->
                    let uu____6656 =
                      let uu____6661 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6661 in
                    (match uu____6656 with
                     | (us_r,uu____6693) ->
                         let uu____6694 =
                           let uu____6699 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6699 in
                         (match uu____6694 with
                          | (us_e,uu____6731) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6734 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6734
                                  us_r in
                              let as_ens =
                                let uu____6736 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6736
                                  us_e in
                              let req =
                                let uu____6740 =
                                  let uu____6741 =
                                    let uu____6742 =
                                      let uu____6753 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6753] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6742 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6741 in
                                uu____6740 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6771 =
                                  let uu____6772 =
                                    let uu____6773 =
                                      let uu____6784 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6784] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6773 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6772 in
                                uu____6771 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6799 =
                                let uu____6802 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6802 in
                              let uu____6803 =
                                let uu____6804 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6804 in
                              (uu____6799, uu____6803)))
                | uu____6807 -> failwith "Impossible"))
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
      (let uu____6833 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6833
       then
         let uu____6834 = FStar_Syntax_Print.term_to_string tm in
         let uu____6835 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6834 uu____6835
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
        (let uu____6853 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6853
         then
           let uu____6854 = FStar_Syntax_Print.term_to_string tm in
           let uu____6855 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6854
             uu____6855
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6860 =
      let uu____6861 =
        let uu____6862 = FStar_Syntax_Subst.compress t in
        uu____6862.FStar_Syntax_Syntax.n in
      match uu____6861 with
      | FStar_Syntax_Syntax.Tm_app uu____6865 -> false
      | uu____6880 -> true in
    if uu____6860
    then t
    else
      (let uu____6882 = FStar_Syntax_Util.head_and_args t in
       match uu____6882 with
       | (head1,args) ->
           let uu____6919 =
             let uu____6920 =
               let uu____6921 = FStar_Syntax_Subst.compress head1 in
               uu____6921.FStar_Syntax_Syntax.n in
             match uu____6920 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6924 -> false in
           if uu____6919
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6946 ->
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
             let uu____6983 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6983 with
             | (formals,uu____6997) ->
                 let n_implicits =
                   let uu____7015 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7091  ->
                             match uu____7091 with
                             | (uu____7098,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7015 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7229 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7229 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7253 =
                     let uu____7254 =
                       let uu____7259 =
                         let uu____7260 = FStar_Util.string_of_int n_expected in
                         let uu____7267 = FStar_Syntax_Print.term_to_string e in
                         let uu____7268 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7260 uu____7267 uu____7268 in
                       let uu____7275 = FStar_TypeChecker_Env.get_range env in
                       (uu____7259, uu____7275) in
                     FStar_Errors.Error uu____7254 in
                   FStar_Exn.raise uu____7253
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___273_7296 =
             match uu___273_7296 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7326 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7326 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7435) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7478,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7511 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7511 with
                           | (v1,uu____7551,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7568 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7568 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7661 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7661)))
                      | (uu____7688,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7734 =
                      let uu____7761 = inst_n_binders t in
                      aux [] uu____7761 bs1 in
                    (match uu____7734 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7832) -> (e, torig, guard)
                          | (uu____7863,[]) when
                              let uu____7894 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7894 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7895 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7927 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7942 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7950 =
      let uu____7953 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7953
        (FStar_List.map
           (fun u  ->
              let uu____7963 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7963 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7950 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7980 = FStar_Util.set_is_empty x in
      if uu____7980
      then []
      else
        (let s =
           let uu____7987 =
             let uu____7990 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7990 in
           FStar_All.pipe_right uu____7987 FStar_Util.set_elements in
         (let uu____7998 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7998
          then
            let uu____7999 =
              let uu____8000 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8000 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7999
          else ());
         (let r =
            let uu____8007 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8007 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8022 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8022
                     then
                       let uu____8023 =
                         let uu____8024 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8024 in
                       let uu____8025 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8026 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8023 uu____8025 uu____8026
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
        let uu____8048 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8048 FStar_Util.fifo_set_elements in
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
        | ([],uu____8080) -> generalized_univ_names
        | (uu____8087,[]) -> explicit_univ_names
        | uu____8094 ->
            let uu____8103 =
              let uu____8104 =
                let uu____8109 =
                  let uu____8110 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____8110 in
                (uu____8109, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____8104 in
            FStar_Exn.raise uu____8103
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
      (let uu____8127 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8127
       then
         let uu____8128 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8128
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8134 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8134
        then
          let uu____8135 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8135
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
        let uu____8205 =
          let uu____8206 =
            FStar_Util.for_all
              (fun uu____8219  ->
                 match uu____8219 with
                 | (uu____8228,uu____8229,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8206 in
        if uu____8205
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8275 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8275
              then
                let uu____8276 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8276
              else ());
             (let c1 =
                let uu____8279 = FStar_TypeChecker_Env.should_verify env in
                if uu____8279
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
              (let uu____8282 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8282
               then
                 let uu____8283 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8283
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8344 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8344 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8474 =
             match uu____8474 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8540 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8540
                   then
                     let uu____8541 =
                       let uu____8542 =
                         let uu____8545 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8545
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8542
                         (FStar_String.concat ", ") in
                     let uu____8572 =
                       let uu____8573 =
                         let uu____8576 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8576
                           (FStar_List.map
                              (fun uu____8604  ->
                                 match uu____8604 with
                                 | (u,t2) ->
                                     let uu____8611 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8612 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8611 uu____8612)) in
                       FStar_All.pipe_right uu____8573
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8541
                       uu____8572
                   else ());
                  (let univs2 =
                     let uu____8619 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8642  ->
                            match uu____8642 with
                            | (uu____8651,t2) ->
                                let uu____8653 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8653)
                       univs1 uu____8619 in
                   let uvs = gen_uvars uvt in
                   (let uu____8676 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8676
                    then
                      let uu____8677 =
                        let uu____8678 =
                          let uu____8681 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8681
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8678
                          (FStar_String.concat ", ") in
                      let uu____8708 =
                        let uu____8709 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8741  ->
                                  match uu____8741 with
                                  | (u,t2) ->
                                      let uu____8748 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8749 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8748 uu____8749)) in
                        FStar_All.pipe_right uu____8709
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8677
                        uu____8708
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8779 =
             let uu____8812 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8812 in
           match uu____8779 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8930 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8930
                 then ()
                 else
                   (let uu____8932 = lec_hd in
                    match uu____8932 with
                    | (lb1,uu____8940,uu____8941) ->
                        let uu____8942 = lec2 in
                        (match uu____8942 with
                         | (lb2,uu____8950,uu____8951) ->
                             let msg =
                               let uu____8953 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8954 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8953 uu____8954 in
                             let uu____8955 =
                               let uu____8956 =
                                 let uu____8961 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8961) in
                               FStar_Errors.Error uu____8956 in
                             FStar_Exn.raise uu____8955)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9072  ->
                           match uu____9072 with
                           | (u,uu____9080) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9102  ->
                                       match uu____9102 with
                                       | (u',uu____9110) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9115 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9115
                 then ()
                 else
                   (let uu____9117 = lec_hd in
                    match uu____9117 with
                    | (lb1,uu____9125,uu____9126) ->
                        let uu____9127 = lec2 in
                        (match uu____9127 with
                         | (lb2,uu____9135,uu____9136) ->
                             let msg =
                               let uu____9138 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9139 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9138 uu____9139 in
                             let uu____9140 =
                               let uu____9141 =
                                 let uu____9146 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____9146) in
                               FStar_Errors.Error uu____9141 in
                             FStar_Exn.raise uu____9140)) in
               let lecs1 =
                 let uu____9156 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9215 = univs_and_uvars_of_lec this_lec in
                        match uu____9215 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9156 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9368 = lec_hd in
                   match uu____9368 with
                   | (lbname,e,c) ->
                       let uu____9378 =
                         let uu____9379 =
                           let uu____9384 =
                             let uu____9385 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9386 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9387 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9385 uu____9386 uu____9387 in
                           let uu____9388 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9384, uu____9388) in
                         FStar_Errors.Error uu____9379 in
                       FStar_Exn.raise uu____9378 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9418  ->
                         match uu____9418 with
                         | (u,k) ->
                             let uu____9431 = FStar_Syntax_Unionfind.find u in
                             (match uu____9431 with
                              | FStar_Pervasives_Native.Some uu____9440 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9447 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9451 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9451 with
                                   | (bs,kres) ->
                                       ((let uu____9489 =
                                           let uu____9490 =
                                             let uu____9493 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9493 in
                                           uu____9490.FStar_Syntax_Syntax.n in
                                         match uu____9489 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9494 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9498 =
                                               let uu____9499 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9499 in
                                             if uu____9498
                                             then fail kres
                                             else ()
                                         | uu____9501 -> fail kres);
                                        (let a =
                                           let uu____9503 =
                                             let uu____9506 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9506 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9503 kres in
                                         let t =
                                           let uu____9510 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9510
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
                      (fun uu____9629  ->
                         match uu____9629 with
                         | (lbname,e,c) ->
                             let uu____9675 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9744 ->
                                   let uu____9759 = (e, c) in
                                   (match uu____9759 with
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
                                                (fun uu____9796  ->
                                                   match uu____9796 with
                                                   | (x,uu____9804) ->
                                                       let uu____9809 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9809)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9819 =
                                                let uu____9820 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9820 in
                                              if uu____9819
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
                                          let uu____9828 =
                                            let uu____9829 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9829.FStar_Syntax_Syntax.n in
                                          match uu____9828 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9852 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9852 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9867 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9869 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9869, gen_tvars)) in
                             (match uu____9675 with
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
        (let uu____10015 = Obj.magic () in ());
        (let uu____10017 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____10017
         then
           let uu____10018 =
             let uu____10019 =
               FStar_List.map
                 (fun uu____10032  ->
                    match uu____10032 with
                    | (lb,uu____10040,uu____10041) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____10019 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____10018
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10062  ->
                match uu____10062 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10091 = gen env is_rec lecs in
           match uu____10091 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10190  ->
                       match uu____10190 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10252 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10252
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10296  ->
                           match uu____10296 with
                           | (l,us,e,c,gvs) ->
                               let uu____10330 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10331 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10332 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10333 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10334 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10330 uu____10331 uu____10332
                                 uu____10333 uu____10334))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10375  ->
                match uu____10375 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10419 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10419, t, c, gvs)) univnames_lecs
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
              (let uu____10462 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10462 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10468 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10468) in
          let is_var e1 =
            let uu____10475 =
              let uu____10476 = FStar_Syntax_Subst.compress e1 in
              uu____10476.FStar_Syntax_Syntax.n in
            match uu____10475 with
            | FStar_Syntax_Syntax.Tm_name uu____10479 -> true
            | uu____10480 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___314_10496 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___314_10496.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___314_10496.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10497 -> e2 in
          let env2 =
            let uu___315_10499 = env1 in
            let uu____10500 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___315_10499.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___315_10499.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___315_10499.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___315_10499.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___315_10499.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___315_10499.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___315_10499.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___315_10499.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___315_10499.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___315_10499.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___315_10499.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___315_10499.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___315_10499.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___315_10499.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___315_10499.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10500;
              FStar_TypeChecker_Env.is_iface =
                (uu___315_10499.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___315_10499.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___315_10499.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___315_10499.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___315_10499.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___315_10499.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___315_10499.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___315_10499.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___315_10499.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___315_10499.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___315_10499.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___315_10499.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___315_10499.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___315_10499.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___315_10499.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___315_10499.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___315_10499.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___315_10499.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10501 = check env2 t1 t2 in
          match uu____10501 with
          | FStar_Pervasives_Native.None  ->
              let uu____10508 =
                let uu____10509 =
                  let uu____10514 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10515 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10514, uu____10515) in
                FStar_Errors.Error uu____10509 in
              FStar_Exn.raise uu____10508
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10522 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10522
                then
                  let uu____10523 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10523
                else ());
               (let uu____10525 = decorate e t2 in (uu____10525, g)))
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
        let uu____10553 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10553
        then
          let uu____10558 = discharge g1 in
          let uu____10559 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10558, uu____10559)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10572 =
               let uu____10573 =
                 let uu____10574 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10574 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10573
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10572
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10576 = destruct_comp c1 in
           match uu____10576 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10593 = FStar_TypeChecker_Env.get_range env in
                 let uu____10594 =
                   let uu____10595 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10596 =
                     let uu____10597 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10598 =
                       let uu____10601 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10601] in
                     uu____10597 :: uu____10598 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10595 uu____10596 in
                 uu____10594 FStar_Pervasives_Native.None uu____10593 in
               ((let uu____10605 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10605
                 then
                   let uu____10606 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10606
                 else ());
                (let g2 =
                   let uu____10609 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10609 in
                 let uu____10610 = discharge g2 in
                 let uu____10611 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10610, uu____10611))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___274_10635 =
        match uu___274_10635 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10643)::[] -> f fst1
        | uu____10660 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10665 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10665
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10674 =
          let uu____10677 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10677 in
        FStar_All.pipe_right uu____10674
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10688 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10688
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___275_10702 =
        match uu___275_10702 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10710)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10729)::[] ->
            let uu____10758 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10758
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10763 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10773 =
          let uu____10780 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10780) in
        let uu____10785 =
          let uu____10794 =
            let uu____10801 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10801) in
          let uu____10806 =
            let uu____10815 =
              let uu____10822 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10822) in
            let uu____10827 =
              let uu____10836 =
                let uu____10843 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10843) in
              let uu____10848 =
                let uu____10857 =
                  let uu____10864 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10864) in
                [uu____10857; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10836 :: uu____10848 in
            uu____10815 :: uu____10827 in
          uu____10794 :: uu____10806 in
        uu____10773 :: uu____10785 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10915 =
            FStar_Util.find_map table
              (fun uu____10928  ->
                 match uu____10928 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10945 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10945
                     else FStar_Pervasives_Native.None) in
          (match uu____10915 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10948 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10952 =
      let uu____10953 = FStar_Syntax_Util.un_uinst l in
      uu____10953.FStar_Syntax_Syntax.n in
    match uu____10952 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10957 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10981)::uu____10982 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10993 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____11000,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11001))::uu____11002 -> bs
      | uu____11019 ->
          let uu____11020 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11020 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11024 =
                 let uu____11025 = FStar_Syntax_Subst.compress t in
                 uu____11025.FStar_Syntax_Syntax.n in
               (match uu____11024 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11029) ->
                    let uu____11046 =
                      FStar_Util.prefix_until
                        (fun uu___276_11086  ->
                           match uu___276_11086 with
                           | (uu____11093,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11094)) ->
                               false
                           | uu____11097 -> true) bs' in
                    (match uu____11046 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11132,uu____11133) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11205,uu____11206) ->
                         let uu____11279 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11297  ->
                                   match uu____11297 with
                                   | (x,uu____11305) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11279
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11352  ->
                                     match uu____11352 with
                                     | (x,i) ->
                                         let uu____11371 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11371, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11381 -> bs))
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
          let uu____11413 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11413
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
        (let uu____11436 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11436
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11438 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11438))
         else ());
        (let fv =
           let uu____11441 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11441
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
         let uu____11449 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___316_11455 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___316_11455.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___316_11455.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___316_11455.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___316_11455.FStar_Syntax_Syntax.sigattrs)
           }), uu____11449))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___277_11465 =
        match uu___277_11465 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11466 -> false in
      let reducibility uu___278_11470 =
        match uu___278_11470 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11471 -> false in
      let assumption uu___279_11475 =
        match uu___279_11475 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11476 -> false in
      let reification uu___280_11480 =
        match uu___280_11480 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11481 -> true
        | uu____11482 -> false in
      let inferred uu___281_11486 =
        match uu___281_11486 with
        | FStar_Syntax_Syntax.Discriminator uu____11487 -> true
        | FStar_Syntax_Syntax.Projector uu____11488 -> true
        | FStar_Syntax_Syntax.RecordType uu____11493 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11502 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11511 -> false in
      let has_eq uu___282_11515 =
        match uu___282_11515 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11516 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11576 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11581 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11585 =
        let uu____11586 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___283_11590  ->
                  match uu___283_11590 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11591 -> false)) in
        FStar_All.pipe_right uu____11586 Prims.op_Negation in
      if uu____11585
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11604 =
            let uu____11605 =
              let uu____11610 =
                let uu____11611 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11611 msg in
              (uu____11610, r) in
            FStar_Errors.Error uu____11605 in
          FStar_Exn.raise uu____11604 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11619 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11623 =
            let uu____11624 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11624 in
          if uu____11623 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11629),uu____11630) ->
              ((let uu____11646 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11646
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11650 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11650
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11656 ->
              let uu____11665 =
                let uu____11666 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11666 in
              if uu____11665 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11672 ->
              let uu____11679 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11679 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11683 ->
              let uu____11690 =
                let uu____11691 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11691 in
              if uu____11690 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11697 ->
              let uu____11698 =
                let uu____11699 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11699 in
              if uu____11698 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11705 ->
              let uu____11706 =
                let uu____11707 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11707 in
              if uu____11706 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11713 ->
              let uu____11726 =
                let uu____11727 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11727 in
              if uu____11726 then err'1 () else ()
          | uu____11733 -> ()))
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
                          let uu____11796 =
                            let uu____11799 =
                              let uu____11800 =
                                let uu____11807 =
                                  let uu____11808 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11808 in
                                (uu____11807, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11800 in
                            FStar_Syntax_Syntax.mk uu____11799 in
                          uu____11796 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11849  ->
                                  match uu____11849 with
                                  | (x,imp) ->
                                      let uu____11860 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11860, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11862 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11862 in
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
                             let uu____11871 =
                               let uu____11872 =
                                 let uu____11873 =
                                   let uu____11874 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11875 =
                                     let uu____11876 =
                                       let uu____11877 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11877 in
                                     [uu____11876] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11874
                                     uu____11875 in
                                 uu____11873 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11872 in
                             FStar_Syntax_Util.refine x uu____11871 in
                           let uu____11880 =
                             let uu___317_11881 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___317_11881.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___317_11881.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11880) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11896 =
                          FStar_List.map
                            (fun uu____11918  ->
                               match uu____11918 with
                               | (x,uu____11930) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11896 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11979  ->
                                match uu____11979 with
                                | (x,uu____11991) ->
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
                             (let uu____12005 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12005)
                               ||
                               (let uu____12007 =
                                  let uu____12008 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12008.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12007) in
                           let quals =
                             let uu____12012 =
                               let uu____12015 =
                                 let uu____12018 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12018
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12022 =
                                 FStar_List.filter
                                   (fun uu___284_12026  ->
                                      match uu___284_12026 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12027 -> false) iquals in
                               FStar_List.append uu____12015 uu____12022 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12012 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12048 =
                                 let uu____12049 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12049 in
                               FStar_Syntax_Syntax.mk_Total uu____12048 in
                             let uu____12050 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12050 in
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
                           (let uu____12053 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12053
                            then
                              let uu____12054 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12054
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
                                             fun uu____12107  ->
                                               match uu____12107 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12131 =
                                                       let uu____12134 =
                                                         let uu____12135 =
                                                           let uu____12142 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12142,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12135 in
                                                       pos uu____12134 in
                                                     (uu____12131, b)
                                                   else
                                                     (let uu____12146 =
                                                        let uu____12149 =
                                                          let uu____12150 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12150 in
                                                        pos uu____12149 in
                                                      (uu____12146, b)))) in
                                   let pat_true =
                                     let uu____12168 =
                                       let uu____12171 =
                                         let uu____12172 =
                                           let uu____12185 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12185, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12172 in
                                       pos uu____12171 in
                                     (uu____12168,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12219 =
                                       let uu____12222 =
                                         let uu____12223 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12223 in
                                       pos uu____12222 in
                                     (uu____12219,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12235 =
                                     let uu____12238 =
                                       let uu____12239 =
                                         let uu____12262 =
                                           let uu____12265 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12266 =
                                             let uu____12269 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12269] in
                                           uu____12265 :: uu____12266 in
                                         (arg_exp, uu____12262) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12239 in
                                     FStar_Syntax_Syntax.mk uu____12238 in
                                   uu____12235 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12276 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12276
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
                                let uu____12284 =
                                  let uu____12289 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12289 in
                                let uu____12290 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12284;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12290
                                } in
                              let impl =
                                let uu____12294 =
                                  let uu____12295 =
                                    let uu____12302 =
                                      let uu____12305 =
                                        let uu____12306 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12306
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12305] in
                                    ((false, [lb]), uu____12302) in
                                  FStar_Syntax_Syntax.Sig_let uu____12295 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12294;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12324 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12324
                               then
                                 let uu____12325 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12325
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
                                fun uu____12367  ->
                                  match uu____12367 with
                                  | (a,uu____12373) ->
                                      let uu____12374 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12374 with
                                       | (field_name,uu____12380) ->
                                           let field_proj_tm =
                                             let uu____12382 =
                                               let uu____12383 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12383 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12382 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12400 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12432  ->
                                    match uu____12432 with
                                    | (x,uu____12440) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12442 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12442 with
                                         | (field_name,uu____12450) ->
                                             let t =
                                               let uu____12452 =
                                                 let uu____12453 =
                                                   let uu____12456 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12456 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12453 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12452 in
                                             let only_decl =
                                               (let uu____12460 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12460)
                                                 ||
                                                 (let uu____12462 =
                                                    let uu____12463 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12463.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12462) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12477 =
                                                   FStar_List.filter
                                                     (fun uu___285_12481  ->
                                                        match uu___285_12481
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12482 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12477
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___286_12495  ->
                                                         match uu___286_12495
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12496 ->
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
                                             ((let uu____12515 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12515
                                               then
                                                 let uu____12516 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12516
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
                                                           fun uu____12564 
                                                             ->
                                                             match uu____12564
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12588
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12588,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12604
                                                                    =
                                                                    let uu____12607
                                                                    =
                                                                    let uu____12608
                                                                    =
                                                                    let uu____12615
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12615,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12608 in
                                                                    pos
                                                                    uu____12607 in
                                                                    (uu____12604,
                                                                    b))
                                                                   else
                                                                    (let uu____12619
                                                                    =
                                                                    let uu____12622
                                                                    =
                                                                    let uu____12623
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12623 in
                                                                    pos
                                                                    uu____12622 in
                                                                    (uu____12619,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12639 =
                                                     let uu____12642 =
                                                       let uu____12643 =
                                                         let uu____12656 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12656,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12643 in
                                                     pos uu____12642 in
                                                   let uu____12665 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12639,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12665) in
                                                 let body =
                                                   let uu____12677 =
                                                     let uu____12680 =
                                                       let uu____12681 =
                                                         let uu____12704 =
                                                           let uu____12707 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12707] in
                                                         (arg_exp,
                                                           uu____12704) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12681 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12680 in
                                                   uu____12677
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12715 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12715
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
                                                   let uu____12722 =
                                                     let uu____12727 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12727 in
                                                   let uu____12728 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12722;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12728
                                                   } in
                                                 let impl =
                                                   let uu____12732 =
                                                     let uu____12733 =
                                                       let uu____12740 =
                                                         let uu____12743 =
                                                           let uu____12744 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12744
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12743] in
                                                       ((false, [lb]),
                                                         uu____12740) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12733 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12732;
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
                                                 (let uu____12762 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12762
                                                  then
                                                    let uu____12763 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12763
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12400 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12803) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12808 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12808 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12830 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12830 with
                    | (formals,uu____12846) ->
                        let uu____12863 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12895 =
                                   let uu____12896 =
                                     let uu____12897 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12897 in
                                   FStar_Ident.lid_equals typ_lid uu____12896 in
                                 if uu____12895
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12916,uvs',tps,typ0,uu____12920,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12939 -> failwith "Impossible"
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
                        (match uu____12863 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13012 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13012 with
                              | (indices,uu____13028) ->
                                  let refine_domain =
                                    let uu____13046 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___287_13051  ->
                                              match uu___287_13051 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13052 -> true
                                              | uu____13061 -> false)) in
                                    if uu____13046
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___288_13069 =
                                      match uu___288_13069 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13072,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13084 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13085 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13085 with
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
                                    let uu____13096 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13096 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13161  ->
                                               fun uu____13162  ->
                                                 match (uu____13161,
                                                         uu____13162)
                                                 with
                                                 | ((x,uu____13180),(x',uu____13182))
                                                     ->
                                                     let uu____13191 =
                                                       let uu____13198 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13198) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13191) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13199 -> []