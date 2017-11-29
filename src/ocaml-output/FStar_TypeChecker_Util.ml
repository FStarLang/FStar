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
                                                | uu____5096 -> true))
                                      | uu____5097 -> false) in
                                 let c21 =
                                   let uu____5101 = should_inline_c1 () in
                                   if uu____5101
                                   then
                                     match (e1opt, b) with
                                     | (FStar_Pervasives_Native.Some
                                        e,FStar_Pervasives_Native.Some bv) ->
                                         let uu____5112 =
                                           subst_c2 "inline all pure" in
                                         (match uu____5112 with
                                          | FStar_Util.Inl (c21,uu____5122)
                                              ->
                                              let c2_typ =
                                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                                  env c21 in
                                              let uu____5128 =
                                                destruct_comp c2_typ in
                                              (match uu____5128 with
                                               | (u_res_t,res_t,wp) ->
                                                   let md =
                                                     FStar_TypeChecker_Env.get_effect_decl
                                                       env
                                                       c2_typ.FStar_Syntax_Syntax.effect_name in
                                                   let wp1 =
                                                     if
                                                       FStar_List.existsb
                                                         (fun uu___270_5145 
                                                            ->
                                                            match uu___270_5145
                                                            with
                                                            | FStar_Syntax_Syntax.RETURN
                                                                 -> true
                                                            | FStar_Syntax_Syntax.PARTIAL_RETURN
                                                                 -> true
                                                            | uu____5146 ->
                                                                false)
                                                         c1_typ.FStar_Syntax_Syntax.flags
                                                     then
                                                       let uu____5147 =
                                                         let uu____5148 =
                                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                                             [u_res_t] env md
                                                             md.FStar_Syntax_Syntax.assume_p in
                                                         let uu____5149 =
                                                           let uu____5150 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               res_t in
                                                           let uu____5151 =
                                                             let uu____5154 =
                                                               let uu____5155
                                                                 =
                                                                 let uu____5156
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    bv in
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   u_res_t1
                                                                   res_t1
                                                                   uu____5156
                                                                   e in
                                                               FStar_Syntax_Syntax.as_arg
                                                                 uu____5155 in
                                                             let uu____5157 =
                                                               let uu____5160
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   wp in
                                                               [uu____5160] in
                                                             uu____5154 ::
                                                               uu____5157 in
                                                           uu____5150 ::
                                                             uu____5151 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____5148
                                                           uu____5149 in
                                                       uu____5147
                                                         FStar_Pervasives_Native.None
                                                         wp.FStar_Syntax_Syntax.pos
                                                     else wp in
                                                   mk_comp md u_res_t res_t
                                                     wp1
                                                     c2_typ.FStar_Syntax_Syntax.flags)
                                          | FStar_Util.Inr uu____5164 -> c2)
                                     | (uu____5169,uu____5170) -> c2
                                   else c2 in
                                 let uu____5180 =
                                   lift_and_destruct env c1 c21 in
                                 (match uu____5180 with
                                  | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                      ->
                                      let bs =
                                        match b with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5237 =
                                              FStar_Syntax_Syntax.null_binder
                                                t1 in
                                            [uu____5237]
                                        | FStar_Pervasives_Native.Some x ->
                                            let uu____5239 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____5239] in
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
                                        let uu____5252 =
                                          FStar_Syntax_Syntax.as_arg r11 in
                                        let uu____5253 =
                                          let uu____5256 =
                                            FStar_Syntax_Syntax.as_arg t1 in
                                          let uu____5257 =
                                            let uu____5260 =
                                              FStar_Syntax_Syntax.as_arg t2 in
                                            let uu____5261 =
                                              let uu____5264 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wp1 in
                                              let uu____5265 =
                                                let uu____5268 =
                                                  let uu____5269 = mk_lam wp2 in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____5269 in
                                                [uu____5268] in
                                              uu____5264 :: uu____5265 in
                                            uu____5260 :: uu____5261 in
                                          uu____5256 :: uu____5257 in
                                        uu____5252 :: uu____5253 in
                                      let wp =
                                        let uu____5273 =
                                          let uu____5274 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t1; u_t2] env md
                                              md.FStar_Syntax_Syntax.bind_wp in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____5274 wp_args in
                                        uu____5273
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
      | uu____5286 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5305 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5309 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5309
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5316 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5316
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5321 = destruct_comp c1 in
                    match uu____5321 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5337 =
                            let uu____5338 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5339 =
                              let uu____5340 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5341 =
                                let uu____5344 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5345 =
                                  let uu____5348 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5348] in
                                uu____5344 :: uu____5345 in
                              uu____5340 :: uu____5341 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5338
                              uu____5339 in
                          uu____5337 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___302_5351 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___302_5351.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___302_5351.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___302_5351.FStar_Syntax_Syntax.cflags);
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
            let uu____5384 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5384
            then (lc, g0)
            else
              ((let uu____5391 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5391
                then
                  let uu____5392 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5393 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5392 uu____5393
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___271_5403  ->
                          match uu___271_5403 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5406 -> [])) in
                let strengthen uu____5412 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5420 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5420 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5427 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5429 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5429) in
                           if uu____5427
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5436 =
                                 let uu____5437 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5437 in
                               FStar_Syntax_Util.comp_set_flags uu____5436
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5443 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5443
                           then
                             let uu____5444 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5445 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5444 uu____5445
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5448 = destruct_comp c2 in
                           match uu____5448 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5464 =
                                   let uu____5465 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5466 =
                                     let uu____5467 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5468 =
                                       let uu____5471 =
                                         let uu____5472 =
                                           let uu____5473 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5473 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5472 in
                                       let uu____5474 =
                                         let uu____5477 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5477] in
                                       uu____5471 :: uu____5474 in
                                     uu____5467 :: uu____5468 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5465
                                     uu____5466 in
                                 uu____5464 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5481 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5481
                                 then
                                   let uu____5482 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5482
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5485 =
                  let uu___303_5486 = lc in
                  let uu____5487 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5488 =
                    let uu____5491 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5493 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5493) in
                    if uu____5491 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5487;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___303_5486.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5488;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5485,
                  (let uu___304_5498 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___304_5498.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___304_5498.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___304_5498.FStar_TypeChecker_Env.implicits)
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
        let uu____5513 =
          let uu____5518 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5519 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5518, uu____5519) in
        match uu____5513 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5528 =
                let uu____5529 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5530 =
                  let uu____5531 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5532 =
                    let uu____5535 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5535] in
                  uu____5531 :: uu____5532 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5529 uu____5530 in
              uu____5528 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5541 =
                let uu____5542 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5543 =
                  let uu____5544 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5545 =
                    let uu____5548 =
                      let uu____5549 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5549 in
                    let uu____5550 =
                      let uu____5553 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5553] in
                    uu____5548 :: uu____5550 in
                  uu____5544 :: uu____5545 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5542 uu____5543 in
              uu____5541 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5559 =
                let uu____5560 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5561 =
                  let uu____5562 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5563 =
                    let uu____5566 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5567 =
                      let uu____5570 =
                        let uu____5571 =
                          let uu____5572 =
                            let uu____5573 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5573] in
                          FStar_Syntax_Util.abs uu____5572 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5571 in
                      [uu____5570] in
                    uu____5566 :: uu____5567 in
                  uu____5562 :: uu____5563 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5560 uu____5561 in
              uu____5559 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5580 = FStar_TypeChecker_Env.get_range env in
              bind uu____5580 env FStar_Pervasives_Native.None
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
          let comp uu____5599 =
            let uu____5600 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5600
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5603 =
                 let uu____5628 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5629 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5628 uu____5629 in
               match uu____5603 with
               | ((md,uu____5631,uu____5632),(u_res_t,res_t,wp_then),
                  (uu____5636,uu____5637,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5675 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5676 =
                       let uu____5677 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5678 =
                         let uu____5679 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5680 =
                           let uu____5683 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5684 =
                             let uu____5687 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5688 =
                               let uu____5691 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5691] in
                             uu____5687 :: uu____5688 in
                           uu____5683 :: uu____5684 in
                         uu____5679 :: uu____5680 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5677 uu____5678 in
                     uu____5676 FStar_Pervasives_Native.None uu____5675 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5697 =
                     let uu____5698 = FStar_Options.split_cases () in
                     uu____5698 > (Prims.parse_int "0") in
                   if uu____5697
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5704 =
                          let uu____5705 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5706 =
                            let uu____5707 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5708 =
                              let uu____5711 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5711] in
                            uu____5707 :: uu____5708 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5705 uu____5706 in
                        uu____5704 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5714 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5714;
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
      let uu____5721 =
        let uu____5722 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5722 in
      FStar_Syntax_Syntax.fvar uu____5721 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5754  ->
                 match uu____5754 with
                 | (uu____5759,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5764 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5766 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5766
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5786 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5787 =
                 let uu____5788 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5789 =
                   let uu____5790 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5791 =
                     let uu____5794 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5795 =
                       let uu____5798 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5799 =
                         let uu____5802 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5802] in
                       uu____5798 :: uu____5799 in
                     uu____5794 :: uu____5795 in
                   uu____5790 :: uu____5791 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5788 uu____5789 in
               uu____5787 FStar_Pervasives_Native.None uu____5786 in
             let default_case =
               let post_k =
                 let uu____5809 =
                   let uu____5816 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5816] in
                 let uu____5817 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5809 uu____5817 in
               let kwp =
                 let uu____5823 =
                   let uu____5830 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5830] in
                 let uu____5831 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5823 uu____5831 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5836 =
                   let uu____5837 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5837] in
                 let uu____5838 =
                   let uu____5839 =
                     let uu____5842 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5842 in
                   let uu____5843 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5839 uu____5843 in
                 FStar_Syntax_Util.abs uu____5836 uu____5838
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
                 (fun uu____5867  ->
                    fun celse  ->
                      match uu____5867 with
                      | (g,cthen) ->
                          let uu____5875 =
                            let uu____5900 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5900 celse in
                          (match uu____5875 with
                           | ((md,uu____5902,uu____5903),(uu____5904,uu____5905,wp_then),
                              (uu____5907,uu____5908,wp_else)) ->
                               let uu____5928 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5928 []))
                 lcases default_case in
             let uu____5929 =
               let uu____5930 = FStar_Options.split_cases () in
               uu____5930 > (Prims.parse_int "0") in
             if uu____5929
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5934 = destruct_comp comp1 in
                match uu____5934 with
                | (uu____5941,uu____5942,wp) ->
                    let wp1 =
                      let uu____5947 =
                        let uu____5948 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5949 =
                          let uu____5950 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5951 =
                            let uu____5954 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5954] in
                          uu____5950 :: uu____5951 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5948 uu____5949 in
                      uu____5947 FStar_Pervasives_Native.None
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
          let uu____5969 =
            ((let uu____5972 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5972) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5974 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5974) in
          if uu____5969
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5983 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5987 =
            ((let uu____5990 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5990) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5987
          then c
          else
            (let uu____5994 = FStar_Syntax_Util.is_partial_return c in
             if uu____5994
             then c
             else
               (let uu____5998 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5998
                then
                  let uu____6001 =
                    let uu____6002 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____6002 in
                  (if uu____6001
                   then
                     let uu____6005 =
                       let uu____6006 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____6007 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____6006 uu____6007 in
                     failwith uu____6005
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____6012 =
                        let uu____6013 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____6013 in
                      if uu____6012
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___305_6018 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___305_6018.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___305_6018.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___305_6018.FStar_Syntax_Syntax.effect_args);
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
                     let uu____6029 =
                       let uu____6032 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____6032
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____6029 in
                   let eq1 =
                     let uu____6036 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____6036 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____6038 =
                     let uu____6039 =
                       let uu____6044 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____6044.FStar_Syntax_Syntax.comp in
                     uu____6039 () in
                   FStar_Syntax_Util.comp_set_flags uu____6038 flags))) in
        let uu____6047 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____6047
        then lc
        else
          (let uu___306_6049 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___306_6049.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___306_6049.FStar_Syntax_Syntax.res_typ);
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
          let uu____6074 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6074 with
          | FStar_Pervasives_Native.None  ->
              let uu____6083 =
                let uu____6084 =
                  let uu____6089 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____6090 = FStar_TypeChecker_Env.get_range env in
                  (uu____6089, uu____6090) in
                FStar_Errors.Error uu____6084 in
              FStar_Exn.raise uu____6083
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
            let uu____6123 =
              let uu____6124 = FStar_Syntax_Subst.compress t2 in
              uu____6124.FStar_Syntax_Syntax.n in
            match uu____6123 with
            | FStar_Syntax_Syntax.Tm_type uu____6127 -> true
            | uu____6128 -> false in
          let uu____6129 =
            let uu____6130 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6130.FStar_Syntax_Syntax.n in
          match uu____6129 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6138 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6149 =
                  let uu____6150 =
                    let uu____6151 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6151 in
                  (FStar_Pervasives_Native.None, uu____6150) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6149 in
              let e1 =
                let uu____6161 =
                  let uu____6162 =
                    let uu____6163 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6163] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6162 in
                uu____6161 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6168 -> (e, lc)
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
              (let uu____6197 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6197 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6220 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6242 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6242, false)
            else
              (let uu____6248 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6248, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6259) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6268 =
                  let uu____6269 =
                    let uu____6274 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6274, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6269 in
                FStar_Exn.raise uu____6268
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___307_6284 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___307_6284.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___307_6284.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___307_6284.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6289 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6289 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___308_6297 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___308_6297.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___308_6297.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___308_6297.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___309_6300 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___309_6300.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___309_6300.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___309_6300.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6306 =
                     let uu____6307 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6307
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6312 =
                          let uu____6313 = FStar_Syntax_Subst.compress f1 in
                          uu____6313.FStar_Syntax_Syntax.n in
                        match uu____6312 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6318,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6320;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6321;_},uu____6322)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___310_6344 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___310_6344.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___310_6344.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___310_6344.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6345 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6350 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6350
                              then
                                let uu____6351 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6352 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6353 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6354 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6351 uu____6352 uu____6353 uu____6354
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6357 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6357 with
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
                                  let uu____6370 = destruct_comp ct in
                                  (match uu____6370 with
                                   | (u_t,uu____6380,uu____6381) ->
                                       let wp =
                                         let uu____6385 =
                                           let uu____6386 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6387 =
                                             let uu____6388 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6389 =
                                               let uu____6392 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6392] in
                                             uu____6388 :: uu____6389 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6386 uu____6387 in
                                         uu____6385
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6396 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6396 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6406 =
                                             let uu____6407 =
                                               let uu____6408 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6408] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6407 in
                                           uu____6406
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6412 =
                                         let uu____6417 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6430 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6431 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6417
                                           uu____6430 e cret uu____6431 in
                                       (match uu____6412 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___311_6437 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___311_6437.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___311_6437.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6439 =
                                                let uu____6440 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6440 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6439
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6451 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6451
                                              then
                                                let uu____6452 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6452
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___272_6462  ->
                             match uu___272_6462 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6465 -> [])) in
                   let lc1 =
                     let uu___312_6467 = lc in
                     let uu____6468 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6468;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___313_6470 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___313_6470.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___313_6470.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___313_6470.FStar_TypeChecker_Env.implicits)
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
        let uu____6493 =
          let uu____6494 =
            let uu____6495 =
              let uu____6496 =
                let uu____6497 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6497 in
              [uu____6496] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6495 in
          uu____6494 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6493 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6504 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6504
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6522 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6537 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6566)::(ens,uu____6568)::uu____6569 ->
                    let uu____6598 =
                      let uu____6601 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6601 in
                    let uu____6602 =
                      let uu____6603 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6603 in
                    (uu____6598, uu____6602)
                | uu____6606 ->
                    let uu____6615 =
                      let uu____6616 =
                        let uu____6621 =
                          let uu____6622 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6622 in
                        (uu____6621, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6616 in
                    FStar_Exn.raise uu____6615)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6638)::uu____6639 ->
                    let uu____6658 =
                      let uu____6663 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6663 in
                    (match uu____6658 with
                     | (us_r,uu____6695) ->
                         let uu____6696 =
                           let uu____6701 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6701 in
                         (match uu____6696 with
                          | (us_e,uu____6733) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6736 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6736
                                  us_r in
                              let as_ens =
                                let uu____6738 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6738
                                  us_e in
                              let req =
                                let uu____6742 =
                                  let uu____6743 =
                                    let uu____6744 =
                                      let uu____6755 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6755] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6744 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6743 in
                                uu____6742 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6773 =
                                  let uu____6774 =
                                    let uu____6775 =
                                      let uu____6786 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6786] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6775 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6774 in
                                uu____6773 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6801 =
                                let uu____6804 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6804 in
                              let uu____6805 =
                                let uu____6806 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6806 in
                              (uu____6801, uu____6805)))
                | uu____6809 -> failwith "Impossible"))
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
      (let uu____6835 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6835
       then
         let uu____6836 = FStar_Syntax_Print.term_to_string tm in
         let uu____6837 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6836 uu____6837
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
        (let uu____6855 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6855
         then
           let uu____6856 = FStar_Syntax_Print.term_to_string tm in
           let uu____6857 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6856
             uu____6857
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6862 =
      let uu____6863 =
        let uu____6864 = FStar_Syntax_Subst.compress t in
        uu____6864.FStar_Syntax_Syntax.n in
      match uu____6863 with
      | FStar_Syntax_Syntax.Tm_app uu____6867 -> false
      | uu____6882 -> true in
    if uu____6862
    then t
    else
      (let uu____6884 = FStar_Syntax_Util.head_and_args t in
       match uu____6884 with
       | (head1,args) ->
           let uu____6921 =
             let uu____6922 =
               let uu____6923 = FStar_Syntax_Subst.compress head1 in
               uu____6923.FStar_Syntax_Syntax.n in
             match uu____6922 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6926 -> false in
           if uu____6921
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6948 ->
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
             let uu____6985 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6985 with
             | (formals,uu____6999) ->
                 let n_implicits =
                   let uu____7017 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7093  ->
                             match uu____7093 with
                             | (uu____7100,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7017 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7231 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7231 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7255 =
                     let uu____7256 =
                       let uu____7261 =
                         let uu____7262 = FStar_Util.string_of_int n_expected in
                         let uu____7269 = FStar_Syntax_Print.term_to_string e in
                         let uu____7270 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7262 uu____7269 uu____7270 in
                       let uu____7277 = FStar_TypeChecker_Env.get_range env in
                       (uu____7261, uu____7277) in
                     FStar_Errors.Error uu____7256 in
                   FStar_Exn.raise uu____7255
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___273_7298 =
             match uu___273_7298 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7328 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7328 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7437) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7480,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7513 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7513 with
                           | (v1,uu____7553,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7570 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7570 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7663 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7663)))
                      | (uu____7690,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7736 =
                      let uu____7763 = inst_n_binders t in
                      aux [] uu____7763 bs1 in
                    (match uu____7736 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7834) -> (e, torig, guard)
                          | (uu____7865,[]) when
                              let uu____7896 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7896 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7897 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7929 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7944 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7952 =
      let uu____7955 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7955
        (FStar_List.map
           (fun u  ->
              let uu____7965 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7965 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7952 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7982 = FStar_Util.set_is_empty x in
      if uu____7982
      then []
      else
        (let s =
           let uu____7989 =
             let uu____7992 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7992 in
           FStar_All.pipe_right uu____7989 FStar_Util.set_elements in
         (let uu____8000 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____8000
          then
            let uu____8001 =
              let uu____8002 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8002 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8001
          else ());
         (let r =
            let uu____8009 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8009 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8024 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8024
                     then
                       let uu____8025 =
                         let uu____8026 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8026 in
                       let uu____8027 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8028 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8025 uu____8027 uu____8028
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
        let uu____8050 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8050 FStar_Util.fifo_set_elements in
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
        | ([],uu____8082) -> generalized_univ_names
        | (uu____8089,[]) -> explicit_univ_names
        | uu____8096 ->
            let uu____8105 =
              let uu____8106 =
                let uu____8111 =
                  let uu____8112 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____8112 in
                (uu____8111, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____8106 in
            FStar_Exn.raise uu____8105
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
      (let uu____8129 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8129
       then
         let uu____8130 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8130
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8136 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8136
        then
          let uu____8137 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8137
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
        let uu____8207 =
          let uu____8208 =
            FStar_Util.for_all
              (fun uu____8221  ->
                 match uu____8221 with
                 | (uu____8230,uu____8231,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8208 in
        if uu____8207
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8277 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8277
              then
                let uu____8278 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8278
              else ());
             (let c1 =
                let uu____8281 = FStar_TypeChecker_Env.should_verify env in
                if uu____8281
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
              (let uu____8284 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8284
               then
                 let uu____8285 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8285
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8346 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8346 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8476 =
             match uu____8476 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8542 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8542
                   then
                     let uu____8543 =
                       let uu____8544 =
                         let uu____8547 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8547
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8544
                         (FStar_String.concat ", ") in
                     let uu____8574 =
                       let uu____8575 =
                         let uu____8578 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8578
                           (FStar_List.map
                              (fun uu____8606  ->
                                 match uu____8606 with
                                 | (u,t2) ->
                                     let uu____8613 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8614 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8613 uu____8614)) in
                       FStar_All.pipe_right uu____8575
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8543
                       uu____8574
                   else ());
                  (let univs2 =
                     let uu____8621 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8644  ->
                            match uu____8644 with
                            | (uu____8653,t2) ->
                                let uu____8655 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8655)
                       univs1 uu____8621 in
                   let uvs = gen_uvars uvt in
                   (let uu____8678 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8678
                    then
                      let uu____8679 =
                        let uu____8680 =
                          let uu____8683 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8683
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8680
                          (FStar_String.concat ", ") in
                      let uu____8710 =
                        let uu____8711 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8743  ->
                                  match uu____8743 with
                                  | (u,t2) ->
                                      let uu____8750 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8751 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8750 uu____8751)) in
                        FStar_All.pipe_right uu____8711
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8679
                        uu____8710
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8781 =
             let uu____8814 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8814 in
           match uu____8781 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8932 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8932
                 then ()
                 else
                   (let uu____8934 = lec_hd in
                    match uu____8934 with
                    | (lb1,uu____8942,uu____8943) ->
                        let uu____8944 = lec2 in
                        (match uu____8944 with
                         | (lb2,uu____8952,uu____8953) ->
                             let msg =
                               let uu____8955 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8956 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8955 uu____8956 in
                             let uu____8957 =
                               let uu____8958 =
                                 let uu____8963 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8963) in
                               FStar_Errors.Error uu____8958 in
                             FStar_Exn.raise uu____8957)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9074  ->
                           match uu____9074 with
                           | (u,uu____9082) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9104  ->
                                       match uu____9104 with
                                       | (u',uu____9112) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9117 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9117
                 then ()
                 else
                   (let uu____9119 = lec_hd in
                    match uu____9119 with
                    | (lb1,uu____9127,uu____9128) ->
                        let uu____9129 = lec2 in
                        (match uu____9129 with
                         | (lb2,uu____9137,uu____9138) ->
                             let msg =
                               let uu____9140 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9141 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9140 uu____9141 in
                             let uu____9142 =
                               let uu____9143 =
                                 let uu____9148 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____9148) in
                               FStar_Errors.Error uu____9143 in
                             FStar_Exn.raise uu____9142)) in
               let lecs1 =
                 let uu____9158 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9217 = univs_and_uvars_of_lec this_lec in
                        match uu____9217 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9158 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9370 = lec_hd in
                   match uu____9370 with
                   | (lbname,e,c) ->
                       let uu____9380 =
                         let uu____9381 =
                           let uu____9386 =
                             let uu____9387 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9388 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9389 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9387 uu____9388 uu____9389 in
                           let uu____9390 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9386, uu____9390) in
                         FStar_Errors.Error uu____9381 in
                       FStar_Exn.raise uu____9380 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9420  ->
                         match uu____9420 with
                         | (u,k) ->
                             let uu____9433 = FStar_Syntax_Unionfind.find u in
                             (match uu____9433 with
                              | FStar_Pervasives_Native.Some uu____9442 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9449 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9453 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9453 with
                                   | (bs,kres) ->
                                       ((let uu____9491 =
                                           let uu____9492 =
                                             let uu____9495 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9495 in
                                           uu____9492.FStar_Syntax_Syntax.n in
                                         match uu____9491 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9496 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9500 =
                                               let uu____9501 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9501 in
                                             if uu____9500
                                             then fail kres
                                             else ()
                                         | uu____9503 -> fail kres);
                                        (let a =
                                           let uu____9505 =
                                             let uu____9508 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9508 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9505 kres in
                                         let t =
                                           let uu____9512 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9512
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
                      (fun uu____9631  ->
                         match uu____9631 with
                         | (lbname,e,c) ->
                             let uu____9677 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9746 ->
                                   let uu____9761 = (e, c) in
                                   (match uu____9761 with
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
                                                (fun uu____9798  ->
                                                   match uu____9798 with
                                                   | (x,uu____9806) ->
                                                       let uu____9811 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9811)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9821 =
                                                let uu____9822 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9822 in
                                              if uu____9821
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
                                          let uu____9830 =
                                            let uu____9831 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9831.FStar_Syntax_Syntax.n in
                                          match uu____9830 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9854 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9854 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9869 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9871 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9871, gen_tvars)) in
                             (match uu____9677 with
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
        (let uu____10017 = Obj.magic () in ());
        (let uu____10019 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____10019
         then
           let uu____10020 =
             let uu____10021 =
               FStar_List.map
                 (fun uu____10034  ->
                    match uu____10034 with
                    | (lb,uu____10042,uu____10043) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____10021 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____10020
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10064  ->
                match uu____10064 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10093 = gen env is_rec lecs in
           match uu____10093 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10192  ->
                       match uu____10192 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10254 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10254
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10298  ->
                           match uu____10298 with
                           | (l,us,e,c,gvs) ->
                               let uu____10332 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10333 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10334 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10335 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10336 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10332 uu____10333 uu____10334
                                 uu____10335 uu____10336))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10377  ->
                match uu____10377 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10421 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10421, t, c, gvs)) univnames_lecs
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
              (let uu____10464 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10464 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10470 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10470) in
          let is_var e1 =
            let uu____10477 =
              let uu____10478 = FStar_Syntax_Subst.compress e1 in
              uu____10478.FStar_Syntax_Syntax.n in
            match uu____10477 with
            | FStar_Syntax_Syntax.Tm_name uu____10481 -> true
            | uu____10482 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___314_10498 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___314_10498.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___314_10498.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10499 -> e2 in
          let env2 =
            let uu___315_10501 = env1 in
            let uu____10502 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___315_10501.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___315_10501.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___315_10501.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___315_10501.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___315_10501.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___315_10501.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___315_10501.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___315_10501.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___315_10501.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___315_10501.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___315_10501.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___315_10501.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___315_10501.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___315_10501.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___315_10501.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10502;
              FStar_TypeChecker_Env.is_iface =
                (uu___315_10501.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___315_10501.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___315_10501.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___315_10501.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___315_10501.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___315_10501.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___315_10501.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___315_10501.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___315_10501.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___315_10501.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___315_10501.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___315_10501.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___315_10501.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___315_10501.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___315_10501.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___315_10501.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___315_10501.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___315_10501.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10503 = check env2 t1 t2 in
          match uu____10503 with
          | FStar_Pervasives_Native.None  ->
              let uu____10510 =
                let uu____10511 =
                  let uu____10516 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10517 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10516, uu____10517) in
                FStar_Errors.Error uu____10511 in
              FStar_Exn.raise uu____10510
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10524 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10524
                then
                  let uu____10525 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10525
                else ());
               (let uu____10527 = decorate e t2 in (uu____10527, g)))
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
        let uu____10555 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10555
        then
          let uu____10560 = discharge g1 in
          let uu____10561 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10560, uu____10561)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10574 =
               let uu____10575 =
                 let uu____10576 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10576 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10575
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10574
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10578 = destruct_comp c1 in
           match uu____10578 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10595 = FStar_TypeChecker_Env.get_range env in
                 let uu____10596 =
                   let uu____10597 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10598 =
                     let uu____10599 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10600 =
                       let uu____10603 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10603] in
                     uu____10599 :: uu____10600 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10597 uu____10598 in
                 uu____10596 FStar_Pervasives_Native.None uu____10595 in
               ((let uu____10607 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10607
                 then
                   let uu____10608 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10608
                 else ());
                (let g2 =
                   let uu____10611 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10611 in
                 let uu____10612 = discharge g2 in
                 let uu____10613 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10612, uu____10613))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___274_10637 =
        match uu___274_10637 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10645)::[] -> f fst1
        | uu____10662 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10667 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10667
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10676 =
          let uu____10679 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10679 in
        FStar_All.pipe_right uu____10676
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10690 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10690
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___275_10704 =
        match uu___275_10704 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10712)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10731)::[] ->
            let uu____10760 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10760
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10765 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10775 =
          let uu____10782 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10782) in
        let uu____10787 =
          let uu____10796 =
            let uu____10803 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10803) in
          let uu____10808 =
            let uu____10817 =
              let uu____10824 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10824) in
            let uu____10829 =
              let uu____10838 =
                let uu____10845 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10845) in
              let uu____10850 =
                let uu____10859 =
                  let uu____10866 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10866) in
                [uu____10859; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10838 :: uu____10850 in
            uu____10817 :: uu____10829 in
          uu____10796 :: uu____10808 in
        uu____10775 :: uu____10787 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10917 =
            FStar_Util.find_map table
              (fun uu____10930  ->
                 match uu____10930 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10947 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10947
                     else FStar_Pervasives_Native.None) in
          (match uu____10917 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10950 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10954 =
      let uu____10955 = FStar_Syntax_Util.un_uinst l in
      uu____10955.FStar_Syntax_Syntax.n in
    match uu____10954 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10959 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10983)::uu____10984 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10995 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____11002,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11003))::uu____11004 -> bs
      | uu____11021 ->
          let uu____11022 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11022 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11026 =
                 let uu____11027 = FStar_Syntax_Subst.compress t in
                 uu____11027.FStar_Syntax_Syntax.n in
               (match uu____11026 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11031) ->
                    let uu____11048 =
                      FStar_Util.prefix_until
                        (fun uu___276_11088  ->
                           match uu___276_11088 with
                           | (uu____11095,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11096)) ->
                               false
                           | uu____11099 -> true) bs' in
                    (match uu____11048 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11134,uu____11135) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11207,uu____11208) ->
                         let uu____11281 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11299  ->
                                   match uu____11299 with
                                   | (x,uu____11307) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11281
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11354  ->
                                     match uu____11354 with
                                     | (x,i) ->
                                         let uu____11373 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11373, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11383 -> bs))
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
          let uu____11415 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11415
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
        (let uu____11438 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11438
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11440 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11440))
         else ());
        (let fv =
           let uu____11443 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11443
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
         let uu____11451 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___316_11457 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___316_11457.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___316_11457.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___316_11457.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___316_11457.FStar_Syntax_Syntax.sigattrs)
           }), uu____11451))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___277_11467 =
        match uu___277_11467 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11468 -> false in
      let reducibility uu___278_11472 =
        match uu___278_11472 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11473 -> false in
      let assumption uu___279_11477 =
        match uu___279_11477 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11478 -> false in
      let reification uu___280_11482 =
        match uu___280_11482 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11483 -> true
        | uu____11484 -> false in
      let inferred uu___281_11488 =
        match uu___281_11488 with
        | FStar_Syntax_Syntax.Discriminator uu____11489 -> true
        | FStar_Syntax_Syntax.Projector uu____11490 -> true
        | FStar_Syntax_Syntax.RecordType uu____11495 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11504 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11513 -> false in
      let has_eq uu___282_11517 =
        match uu___282_11517 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11518 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11578 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11583 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11587 =
        let uu____11588 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___283_11592  ->
                  match uu___283_11592 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11593 -> false)) in
        FStar_All.pipe_right uu____11588 Prims.op_Negation in
      if uu____11587
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11606 =
            let uu____11607 =
              let uu____11612 =
                let uu____11613 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11613 msg in
              (uu____11612, r) in
            FStar_Errors.Error uu____11607 in
          FStar_Exn.raise uu____11606 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11621 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11625 =
            let uu____11626 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11626 in
          if uu____11625 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11631),uu____11632) ->
              ((let uu____11648 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11648
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11652 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11652
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11658 ->
              let uu____11667 =
                let uu____11668 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11668 in
              if uu____11667 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11674 ->
              let uu____11681 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11681 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11685 ->
              let uu____11692 =
                let uu____11693 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11693 in
              if uu____11692 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11699 ->
              let uu____11700 =
                let uu____11701 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11701 in
              if uu____11700 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11707 ->
              let uu____11708 =
                let uu____11709 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11709 in
              if uu____11708 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11715 ->
              let uu____11728 =
                let uu____11729 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11729 in
              if uu____11728 then err'1 () else ()
          | uu____11735 -> ()))
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
                          let uu____11798 =
                            let uu____11801 =
                              let uu____11802 =
                                let uu____11809 =
                                  let uu____11810 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11810 in
                                (uu____11809, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11802 in
                            FStar_Syntax_Syntax.mk uu____11801 in
                          uu____11798 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11851  ->
                                  match uu____11851 with
                                  | (x,imp) ->
                                      let uu____11862 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11862, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11864 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11864 in
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
                             let uu____11873 =
                               let uu____11874 =
                                 let uu____11875 =
                                   let uu____11876 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11877 =
                                     let uu____11878 =
                                       let uu____11879 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11879 in
                                     [uu____11878] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11876
                                     uu____11877 in
                                 uu____11875 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11874 in
                             FStar_Syntax_Util.refine x uu____11873 in
                           let uu____11882 =
                             let uu___317_11883 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___317_11883.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___317_11883.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11882) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11898 =
                          FStar_List.map
                            (fun uu____11920  ->
                               match uu____11920 with
                               | (x,uu____11932) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11898 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11981  ->
                                match uu____11981 with
                                | (x,uu____11993) ->
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
                             (let uu____12007 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12007)
                               ||
                               (let uu____12009 =
                                  let uu____12010 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12010.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12009) in
                           let quals =
                             let uu____12014 =
                               let uu____12017 =
                                 let uu____12020 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12020
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12024 =
                                 FStar_List.filter
                                   (fun uu___284_12028  ->
                                      match uu___284_12028 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12029 -> false) iquals in
                               FStar_List.append uu____12017 uu____12024 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12014 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12050 =
                                 let uu____12051 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12051 in
                               FStar_Syntax_Syntax.mk_Total uu____12050 in
                             let uu____12052 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12052 in
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
                           (let uu____12055 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12055
                            then
                              let uu____12056 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12056
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
                                             fun uu____12109  ->
                                               match uu____12109 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12133 =
                                                       let uu____12136 =
                                                         let uu____12137 =
                                                           let uu____12144 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12144,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12137 in
                                                       pos uu____12136 in
                                                     (uu____12133, b)
                                                   else
                                                     (let uu____12148 =
                                                        let uu____12151 =
                                                          let uu____12152 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12152 in
                                                        pos uu____12151 in
                                                      (uu____12148, b)))) in
                                   let pat_true =
                                     let uu____12170 =
                                       let uu____12173 =
                                         let uu____12174 =
                                           let uu____12187 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12187, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12174 in
                                       pos uu____12173 in
                                     (uu____12170,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12221 =
                                       let uu____12224 =
                                         let uu____12225 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12225 in
                                       pos uu____12224 in
                                     (uu____12221,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12237 =
                                     let uu____12240 =
                                       let uu____12241 =
                                         let uu____12264 =
                                           let uu____12267 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12268 =
                                             let uu____12271 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12271] in
                                           uu____12267 :: uu____12268 in
                                         (arg_exp, uu____12264) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12241 in
                                     FStar_Syntax_Syntax.mk uu____12240 in
                                   uu____12237 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12278 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12278
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
                                let uu____12286 =
                                  let uu____12291 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12291 in
                                let uu____12292 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12286;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12292
                                } in
                              let impl =
                                let uu____12296 =
                                  let uu____12297 =
                                    let uu____12304 =
                                      let uu____12307 =
                                        let uu____12308 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12308
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12307] in
                                    ((false, [lb]), uu____12304) in
                                  FStar_Syntax_Syntax.Sig_let uu____12297 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12296;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12326 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12326
                               then
                                 let uu____12327 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12327
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
                                fun uu____12369  ->
                                  match uu____12369 with
                                  | (a,uu____12375) ->
                                      let uu____12376 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12376 with
                                       | (field_name,uu____12382) ->
                                           let field_proj_tm =
                                             let uu____12384 =
                                               let uu____12385 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12385 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12384 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12402 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12434  ->
                                    match uu____12434 with
                                    | (x,uu____12442) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12444 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12444 with
                                         | (field_name,uu____12452) ->
                                             let t =
                                               let uu____12454 =
                                                 let uu____12455 =
                                                   let uu____12458 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12458 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12455 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12454 in
                                             let only_decl =
                                               (let uu____12462 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12462)
                                                 ||
                                                 (let uu____12464 =
                                                    let uu____12465 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12465.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12464) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12479 =
                                                   FStar_List.filter
                                                     (fun uu___285_12483  ->
                                                        match uu___285_12483
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12484 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12479
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___286_12497  ->
                                                         match uu___286_12497
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12498 ->
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
                                             ((let uu____12517 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12517
                                               then
                                                 let uu____12518 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12518
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
                                                           fun uu____12566 
                                                             ->
                                                             match uu____12566
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12590
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12590,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12606
                                                                    =
                                                                    let uu____12609
                                                                    =
                                                                    let uu____12610
                                                                    =
                                                                    let uu____12617
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12617,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12610 in
                                                                    pos
                                                                    uu____12609 in
                                                                    (uu____12606,
                                                                    b))
                                                                   else
                                                                    (let uu____12621
                                                                    =
                                                                    let uu____12624
                                                                    =
                                                                    let uu____12625
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12625 in
                                                                    pos
                                                                    uu____12624 in
                                                                    (uu____12621,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12641 =
                                                     let uu____12644 =
                                                       let uu____12645 =
                                                         let uu____12658 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12658,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12645 in
                                                     pos uu____12644 in
                                                   let uu____12667 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12641,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12667) in
                                                 let body =
                                                   let uu____12679 =
                                                     let uu____12682 =
                                                       let uu____12683 =
                                                         let uu____12706 =
                                                           let uu____12709 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12709] in
                                                         (arg_exp,
                                                           uu____12706) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12683 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12682 in
                                                   uu____12679
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12717 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12717
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
                                                   let uu____12724 =
                                                     let uu____12729 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12729 in
                                                   let uu____12730 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12724;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12730
                                                   } in
                                                 let impl =
                                                   let uu____12734 =
                                                     let uu____12735 =
                                                       let uu____12742 =
                                                         let uu____12745 =
                                                           let uu____12746 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12746
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12745] in
                                                       ((false, [lb]),
                                                         uu____12742) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12735 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12734;
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
                                                 (let uu____12764 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12764
                                                  then
                                                    let uu____12765 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12765
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12402 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12805) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12810 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12810 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12832 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12832 with
                    | (formals,uu____12848) ->
                        let uu____12865 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12897 =
                                   let uu____12898 =
                                     let uu____12899 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12899 in
                                   FStar_Ident.lid_equals typ_lid uu____12898 in
                                 if uu____12897
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12918,uvs',tps,typ0,uu____12922,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12941 -> failwith "Impossible"
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
                        (match uu____12865 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13014 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13014 with
                              | (indices,uu____13030) ->
                                  let refine_domain =
                                    let uu____13048 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___287_13053  ->
                                              match uu___287_13053 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13054 -> true
                                              | uu____13063 -> false)) in
                                    if uu____13048
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___288_13071 =
                                      match uu___288_13071 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13074,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13086 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13087 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13087 with
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
                                    let uu____13098 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13098 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13163  ->
                                               fun uu____13164  ->
                                                 match (uu____13163,
                                                         uu____13164)
                                                 with
                                                 | ((x,uu____13182),(x',uu____13184))
                                                     ->
                                                     let uu____13193 =
                                                       let uu____13200 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13200) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13193) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13201 -> []