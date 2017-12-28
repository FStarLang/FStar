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
      FStar_Errors.log_issue uu____17 uu____18
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____26 =
      let uu____27 = FStar_Syntax_Subst.compress t in
      uu____27.FStar_Syntax_Syntax.n in
    match uu____26 with
    | FStar_Syntax_Syntax.Tm_type uu____30 -> true
    | uu____31 -> false
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
        let uu____73 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____75 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____75) in
        if uu____73
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____77 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____77 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____84 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____84
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___78_93  ->
    match uu___78_93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____95);
        FStar_Syntax_Syntax.pos = uu____96;
        FStar_Syntax_Syntax.vars = uu____97;_} -> uv
    | uu____124 -> failwith "Impossible"
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
          let uu____149 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____149 with
          | FStar_Pervasives_Native.Some (uu____172::(tm,uu____174)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____226 ->
              let uu____237 = new_uvar_aux env k in
              (match uu____237 with
               | (t,u) ->
                   let g =
                     let uu___102_257 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u in
                         (reason, env, uu____286, t, k, r) in
                       [uu____273] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___102_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___102_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___102_257.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____258
                     } in
                   let uu____311 =
                     let uu____318 =
                       let uu____323 = as_uvar u in (uu____323, r) in
                     [uu____318] in
                   (t, uu____311, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____351 =
        let uu____352 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____352 in
      if uu____351
      then
        let us =
          let uu____358 =
            let uu____361 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____379  ->
                 match uu____379 with
                 | (x,uu____385) -> FStar_Syntax_Print.uvar_to_string x)
              uu____361 in
          FStar_All.pipe_right uu____358 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____392 =
            let uu____397 =
              let uu____398 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____398 in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____397) in
          FStar_Errors.log_issue r uu____392);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____411  ->
      match uu____411 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____421;
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
                   let uu____467 =
                     let uu____468 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____468.FStar_Syntax_Syntax.n in
                   match uu____467 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____475 = FStar_Syntax_Util.type_u () in
                       (match uu____475 with
                        | (k,uu____485) ->
                            let t2 =
                              let uu____487 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____487
                                FStar_Pervasives_Native.fst in
                            ((let uu___103_497 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___103_497.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___103_497.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____498 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____535) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____542) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____605) ->
                       let uu____626 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____686  ->
                                 fun uu____687  ->
                                   match (uu____686, uu____687) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____765 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____765 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____626 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____877 = aux must_check_ty1 scope body in
                            (match uu____877 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____906 =
                                         FStar_Options.ml_ish () in
                                       if uu____906
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____913 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____913
                                   then
                                     let uu____914 =
                                       FStar_Range.string_of_range r in
                                     let uu____915 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____916 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____914 uu____915 uu____916
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____926 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____940 =
                            let uu____945 =
                              let uu____946 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____946
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____945 in
                          (uu____940, false)) in
                 let uu____959 =
                   let uu____968 = t_binders env in aux false uu____968 e in
                 match uu____959 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____993 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____993
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____997 =
                                let uu____1002 =
                                  let uu____1003 =
                                    FStar_Syntax_Print.comp_to_string c in
                                  FStar_Util.format1
                                    "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                    uu____1003 in
                                (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                  uu____1002) in
                              FStar_Errors.raise_error uu____997 rng)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1011 ->
               let uu____1012 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1012 with
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
            let uu____1092 =
              let uu____1097 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
              match uu____1097 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1102;
                  FStar_Syntax_Syntax.vars = uu____1103;_} ->
                  let uu____1106 = FStar_Syntax_Util.type_u () in
                  (match uu____1106 with
                   | (t,uu____1116) ->
                       let uu____1117 = new_uvar env1 t in
                       (uu____1117, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t in
            match uu____1092 with
            | (t_x,guard) ->
                ((let uu___104_1126 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___104_1126.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___104_1126.FStar_Syntax_Syntax.index);
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
                  | uu____1195 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1203) ->
                let uu____1208 = FStar_Syntax_Util.type_u () in
                (match uu____1208 with
                 | (k,uu____1234) ->
                     let t = new_uvar env1 k in
                     let x1 =
                       let uu___105_1237 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_1237.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_1237.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       } in
                     let uu____1238 =
                       let uu____1243 =
                         FStar_TypeChecker_Env.all_binders env1 in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1243 t in
                     (match uu____1238 with
                      | (e,u) ->
                          let p2 =
                            let uu___106_1269 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___106_1269.FStar_Syntax_Syntax.p)
                            } in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1279 = check_bv env1 x in
                (match uu____1279 with
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
                let uu____1320 = check_bv env1 x in
                (match uu____1320 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1 in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1377 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1513  ->
                          fun uu____1514  ->
                            match (uu____1513, uu____1514) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1712 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2 in
                                (match uu____1712 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     let uu____1788 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard' in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1788, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, [])) in
                (match uu____1377 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1919 =
                         let uu____1922 =
                           let uu____1923 =
                             let uu____1930 =
                               let uu____1933 =
                                 let uu____1934 =
                                   FStar_Syntax_Syntax.fv_to_tm fv in
                                 let uu____1935 =
                                   FStar_All.pipe_right args FStar_List.rev in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1934
                                   uu____1935 in
                               uu____1933 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p in
                             (uu____1930,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app)) in
                           FStar_Syntax_Syntax.Tm_meta uu____1923 in
                         FStar_Syntax_Syntax.mk uu____1922 in
                       uu____1919 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     let uu____1947 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu____1958 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu____1969 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu____1947, uu____1958, uu____1969, env2, e, guard,
                       (let uu___107_1991 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___107_1991.FStar_Syntax_Syntax.p)
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
                    (fun uu____2075  ->
                       match uu____2075 with
                       | (p2,imp) ->
                           let uu____2094 = elaborate_pat env1 p2 in
                           (uu____2094, imp)) pats in
                let uu____2099 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2099 with
                 | (uu____2106,t) ->
                     let uu____2108 = FStar_Syntax_Util.arrow_formals t in
                     (match uu____2108 with
                      | (f,uu____2124) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2246::uu____2247) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments")
                                  (FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | (uu____2298::uu____2299,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2377  ->
                                        match uu____2377 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2404 =
                                                     let uu____2407 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2407 in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2404
                                                     FStar_Syntax_Syntax.tun in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                 let uu____2409 =
                                                   maybe_dot inaccessible a r in
                                                 (uu____2409, true)
                                             | uu____2414 ->
                                                 let uu____2417 =
                                                   let uu____2422 =
                                                     let uu____2423 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2423 in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2422) in
                                                 FStar_Errors.raise_error
                                                   uu____2417
                                                   (FStar_Ident.range_of_lid
                                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2497,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2498)) when p_imp ->
                                     let uu____2501 = aux formals' pats' in
                                     (p2, true) :: uu____2501
                                 | (uu____2518,FStar_Pervasives_Native.Some
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
                                     let uu____2526 = aux formals' pats2 in
                                     (p3, true) :: uu____2526
                                 | (uu____2543,imp) ->
                                     let uu____2549 =
                                       let uu____2556 =
                                         FStar_Syntax_Syntax.is_implicit imp in
                                       (p2, uu____2556) in
                                     let uu____2559 = aux formals' pats' in
                                     uu____2549 :: uu____2559) in
                          let uu___108_2574 = p1 in
                          let uu____2577 =
                            let uu____2578 =
                              let uu____2591 = aux f pats1 in
                              (fv, uu____2591) in
                            FStar_Syntax_Syntax.Pat_cons uu____2578 in
                          {
                            FStar_Syntax_Syntax.v = uu____2577;
                            FStar_Syntax_Syntax.p =
                              (uu___108_2574.FStar_Syntax_Syntax.p)
                          }))
            | uu____2608 -> p1 in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu____2644 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
            match uu____2644 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2702 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu____2702 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2728 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                     FStar_Errors.raise_error uu____2728
                       p3.FStar_Syntax_Syntax.p
                 | uu____2751 -> (b, a, w, arg, guard, p3)) in
          let uu____2760 = one_pat true env p in
          match uu____2760 with
          | (b,uu____2790,uu____2791,tm,guard,p1) -> (b, tm, guard, p1)
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
          | (uu____2837,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2839)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2844,uu____2845) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2849 =
                    let uu____2850 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2851 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2850 uu____2851 in
                  failwith uu____2849)
               else ();
               (let uu____2854 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2854
                then
                  let uu____2855 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2856 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2855
                    uu____2856
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___109_2860 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___109_2860.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___109_2860.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2864 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2864
                then
                  let uu____2865 =
                    let uu____2866 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2867 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2866 uu____2867 in
                  failwith uu____2865
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___110_2871 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___110_2871.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___110_2871.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2873),uu____2874) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2896 =
                  let uu____2897 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2897 in
                if uu____2896
                then
                  let uu____2898 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2898
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2917;
                FStar_Syntax_Syntax.vars = uu____2918;_},args))
              ->
              ((let uu____2957 =
                  let uu____2958 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2958 Prims.op_Negation in
                if uu____2957
                then
                  let uu____2959 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2959
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3095)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3170) ->
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
                       | ((e2,imp),uu____3207) ->
                           let pat =
                             let uu____3229 = aux argpat e2 in
                             let uu____3230 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3229, uu____3230) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3235 ->
                      let uu____3258 =
                        let uu____3259 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3260 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3259 uu____3260 in
                      failwith uu____3258 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3272;
                     FStar_Syntax_Syntax.vars = uu____3273;_},uu____3274);
                FStar_Syntax_Syntax.pos = uu____3275;
                FStar_Syntax_Syntax.vars = uu____3276;_},args))
              ->
              ((let uu____3319 =
                  let uu____3320 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3320 Prims.op_Negation in
                if uu____3319
                then
                  let uu____3321 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3321
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3457)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3532) ->
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
                       | ((e2,imp),uu____3569) ->
                           let pat =
                             let uu____3591 = aux argpat e2 in
                             let uu____3592 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3591, uu____3592) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3597 ->
                      let uu____3620 =
                        let uu____3621 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3622 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3621 uu____3622 in
                      failwith uu____3620 in
                match_args [] args argpats))
          | uu____3631 ->
              let uu____3636 =
                let uu____3637 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3638 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3639 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3637 uu____3638 uu____3639 in
              failwith uu____3636 in
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
    let pat_as_arg uu____3676 =
      match uu____3676 with
      | (p,i) ->
          let uu____3693 = decorated_pattern_as_term p in
          (match uu____3693 with
           | (vars,te) ->
               let uu____3716 =
                 let uu____3721 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3721) in
               (vars, uu____3716)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3735 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3735)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3739 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3739)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3743 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3743)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3764 =
          let uu____3779 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3779 FStar_List.unzip in
        (match uu____3764 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3889 =
               let uu____3890 =
                 let uu____3891 =
                   let uu____3906 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3906, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3891 in
               mk1 uu____3890 in
             (vars1, uu____3889))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let comp_univ_opt:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3936,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3946,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3960 -> FStar_Pervasives_Native.Some hd1)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3984)::[] -> wp
      | uu____4001 ->
          let uu____4010 =
            let uu____4011 =
              let uu____4012 =
                FStar_List.map
                  (fun uu____4022  ->
                     match uu____4022 with
                     | (x,uu____4028) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____4012 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4011 in
          failwith uu____4010 in
    let uu____4033 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____4033, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4047 = destruct_comp c in
        match uu____4047 with
        | (u,uu____4055,wp) ->
            let uu____4057 =
              let uu____4066 =
                let uu____4067 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____4067 in
              [uu____4066] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4057;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4077 =
          let uu____4084 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____4085 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____4084 uu____4085 in
        match uu____4077 with | (m,uu____4087,uu____4088) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4098 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____4098
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
        let uu____4135 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4135 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4172 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4172 with
             | (a,kwp) ->
                 let uu____4203 = destruct_comp m1 in
                 let uu____4210 = destruct_comp m2 in
                 ((md, a, kwp), uu____4203, uu____4210))
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
          fun flags1  ->
            let uu____4272 =
              let uu____4273 =
                let uu____4282 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4282] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4273;
                FStar_Syntax_Syntax.flags = flags1
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4272
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
        fun flags1  ->
          if FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
let subst_lcomp:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst1  ->
    fun lc  ->
      let uu___111_4321 = lc in
      let uu____4322 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___111_4321.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4322;
        FStar_Syntax_Syntax.cflags =
          (uu___111_4321.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4327  ->
             let uu____4328 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4328)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4332 =
      let uu____4333 = FStar_Syntax_Subst.compress t in
      uu____4333.FStar_Syntax_Syntax.n in
    match uu____4332 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4336 -> true
    | uu____4349 -> false
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
              let uu____4387 =
                let uu____4388 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4388 in
              if uu____4387
              then f
              else (let uu____4390 = reason1 () in label uu____4390 r f)
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
            let uu___112_4401 = g in
            let uu____4402 =
              let uu____4403 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4403 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4402;
              FStar_TypeChecker_Env.deferred =
                (uu___112_4401.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___112_4401.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___112_4401.FStar_TypeChecker_Env.implicits)
            }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4417 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4417
        then c
        else
          (let uu____4419 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4419
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4458 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4458] in
                       let us =
                         let uu____4462 =
                           let uu____4465 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4465] in
                         u_res :: uu____4462 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4469 =
                         let uu____4470 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4471 =
                           let uu____4472 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4473 =
                             let uu____4476 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4477 =
                               let uu____4480 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4480] in
                             uu____4476 :: uu____4477 in
                           uu____4472 :: uu____4473 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4470 uu____4471 in
                       uu____4469 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4484 = destruct_comp c1 in
              match uu____4484 with
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
        let close1 uu____4512 =
          let uu____4513 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4513 in
        let uu___113_4514 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___113_4514.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___113_4514.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___113_4514.FStar_Syntax_Syntax.cflags);
          FStar_Syntax_Syntax.comp = close1
        }
let should_not_inline_lc: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___79_4521  ->
            match uu___79_4521 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4522 -> false))
let should_return:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____4538 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
                 Prims.op_Negation uu____4538))
               &&
               (let uu____4545 = FStar_Syntax_Util.head_and_args' e in
                match uu____4545 with
                | (head1,uu____4559) ->
                    let uu____4576 =
                      let uu____4577 = FStar_Syntax_Util.un_uinst head1 in
                      uu____4577.FStar_Syntax_Syntax.n in
                    (match uu____4576 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4581 =
                           let uu____4582 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4582 in
                         Prims.op_Negation uu____4581
                     | uu____4583 -> true)))
              &&
              (let uu____4585 = should_not_inline_lc lc in
               Prims.op_Negation uu____4585)
let return_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____4603 =
              let uu____4604 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid in
              FStar_All.pipe_left Prims.op_Negation uu____4604 in
            if uu____4603
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4606 = FStar_Syntax_Util.is_unit t in
               if uu____4606
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t in
                  let wp =
                    let uu____4612 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4612
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4614 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid in
                       match uu____4614 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp in
                           let uu____4622 =
                             let uu____4623 =
                               let uu____4624 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                               let uu____4625 =
                                 let uu____4626 =
                                   FStar_Syntax_Syntax.as_arg t in
                                 let uu____4627 =
                                   let uu____4630 =
                                     FStar_Syntax_Syntax.as_arg v1 in
                                   [uu____4630] in
                                 uu____4626 :: uu____4627 in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4624
                                 uu____4625 in
                             uu____4623 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4622) in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
          (let uu____4634 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return") in
           if uu____4634
           then
             let uu____4635 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
             let uu____4636 = FStar_Syntax_Print.term_to_string v1 in
             let uu____4637 =
               FStar_TypeChecker_Normalize.comp_to_string env c in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4635 uu____4636 uu____4637
           else ());
          c
let weaken_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    let uu____4648 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___80_4652  ->
              match uu___80_4652 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4653 -> false)) in
    if uu____4648
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___81_4662  ->
              match uu___81_4662 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
let weaken_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4675 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4675
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let uu____4678 = destruct_comp c1 in
           match uu____4678 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name in
               let wp1 =
                 let uu____4692 =
                   let uu____4693 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p in
                   let uu____4694 =
                     let uu____4695 = FStar_Syntax_Syntax.as_arg res_t in
                     let uu____4696 =
                       let uu____4699 = FStar_Syntax_Syntax.as_arg formula in
                       let uu____4700 =
                         let uu____4703 = FStar_Syntax_Syntax.as_arg wp in
                         [uu____4703] in
                       uu____4699 :: uu____4700 in
                     uu____4695 :: uu____4696 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4693 uu____4694 in
                 uu____4692 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos in
               let uu____4706 = weaken_flags c1.FStar_Syntax_Syntax.flags in
               mk_comp md u_res_t res_t wp1 uu____4706)
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4723 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4727 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____4727
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1) in
        let uu___114_4734 = lc in
        let uu____4735 = weaken_flags lc.FStar_Syntax_Syntax.cflags in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___114_4734.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___114_4734.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags = uu____4735;
          FStar_Syntax_Syntax.comp = weaken
        }
let lcomp_has_trivial_postcondition: FStar_Syntax_Syntax.lcomp -> Prims.bool
  =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___82_4742  ->
            match uu___82_4742 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4743 -> false) lc.FStar_Syntax_Syntax.cflags)
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
          fun uu____4760  ->
            match uu____4760 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____4775 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____4775
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4782 = FStar_Syntax_Util.is_total_lcomp lc11 in
                       if uu____4782
                       then
                         let uu____4785 =
                           FStar_Syntax_Util.is_total_lcomp lc21 in
                         (if uu____4785
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4789 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21 in
                             if uu____4789
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4794 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21) in
                          if uu____4794
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____4798 = lcomp_has_trivial_postcondition lc21 in
                     if uu____4798
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1) in
                ((let uu____4803 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4803
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4806 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4808 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4809 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4806 uu____4808 bstr uu____4809
                  else ());
                 (let bind_it uu____4814 =
                    let uu____4815 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4815
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4825 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4825
                        then
                          let uu____4826 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4828 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4829 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4830 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4831 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4826 uu____4828 uu____4829 uu____4830
                            uu____4831
                        else ());
                       (let aux uu____4846 =
                          let uu____4847 = FStar_Syntax_Util.is_trivial_wp c1 in
                          if uu____4847
                          then
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Util.Inl (c2, "trivial no binder")
                            | FStar_Pervasives_Native.Some uu____4876 ->
                                let uu____4877 =
                                  FStar_Syntax_Util.is_ml_comp c2 in
                                (if uu____4877
                                 then FStar_Util.Inl (c2, "trivial ml")
                                 else
                                   FStar_Util.Inr
                                     "c1 trivial; but c2 is not ML")
                          else
                            (let uu____4904 =
                               (FStar_Syntax_Util.is_ml_comp c1) &&
                                 (FStar_Syntax_Util.is_ml_comp c2) in
                             if uu____4904
                             then FStar_Util.Inl (c2, "both ml")
                             else
                               FStar_Util.Inr
                                 "c1 not trivial, and both are not ML") in
                        let subst_c2 reason =
                          match (e1opt, b) with
                          | (FStar_Pervasives_Native.Some
                             e,FStar_Pervasives_Native.Some x) ->
                              let uu____4960 =
                                let uu____4965 =
                                  FStar_Syntax_Subst.subst_comp
                                    [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                (uu____4965, reason) in
                              FStar_Util.Inl uu____4960
                          | uu____4970 -> aux () in
                        let try_simplify uu____4992 =
                          let rec maybe_close t x c =
                            let uu____5003 =
                              let uu____5004 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____5004.FStar_Syntax_Syntax.n in
                            match uu____5003 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____5008) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____5014 -> c in
                          let uu____5015 =
                            let uu____5016 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____5016 in
                          if uu____5015
                          then
                            let uu____5029 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____5029
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____5049 =
                                  FStar_TypeChecker_Env.get_range env in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                    "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                  uu____5049))
                          else
                            (let uu____5061 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____5061
                             then subst_c2 "both total"
                             else
                               (let uu____5073 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____5073
                                then
                                  let uu____5084 =
                                    let uu____5089 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____5089, "both gtot") in
                                  FStar_Util.Inl uu____5084
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____5115 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____5117 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____5117) in
                                       if uu____5115
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___115_5130 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___115_5130.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___115_5130.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____5131 =
                                           let uu____5136 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____5136, "c1 Tot") in
                                         FStar_Util.Inl uu____5131
                                       else aux ()
                                   | uu____5142 -> aux ()))) in
                        let uu____5151 = try_simplify () in
                        match uu____5151 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____5175 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____5175
                              then
                                let uu____5176 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____5177 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____5178 =
                                  FStar_Syntax_Print.comp_to_string c in
                                let uu____5179 =
                                  FStar_Syntax_Print.lid_to_string joined_eff in
                                FStar_Util.print5
                                  "Simplified (because %s) bind c1: %s\n\nc2: %s\n\nto c: %s\n\nWith effect lid: %s\n\n"
                                  reason uu____5176 uu____5177 uu____5178
                                  uu____5179
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____5189 = destruct_comp c1_typ in
                            (match uu____5189 with
                             | (u_res_t1,res_t1,uu____5198) ->
                                 let c21 =
                                   let uu____5202 =
                                     (FStar_Option.isSome b) &&
                                       (should_return env e1opt lc11) in
                                   if uu____5202
                                   then
                                     let e = FStar_Option.get e1opt in
                                     let bv = FStar_Option.get b in
                                     let uu____5207 =
                                       subst_c2 "inline all pure" in
                                     match uu____5207 with
                                     | FStar_Util.Inr _reason -> c2
                                     | FStar_Util.Inl (c21,uu____5224) ->
                                         let uu____5229 =
                                           let uu____5230 =
                                             FStar_Syntax_Util.is_partial_return
                                               c1 in
                                           Prims.op_Negation uu____5230 in
                                         (if uu____5229
                                          then
                                            let x_eq_e =
                                              let uu____5234 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  bv in
                                              FStar_Syntax_Util.mk_eq2
                                                u_res_t1 res_t1 e uu____5234 in
                                            weaken_comp env c21 x_eq_e
                                          else c21)
                                   else c2 in
                                 let uu____5237 =
                                   lift_and_destruct env c1 c21 in
                                 (match uu____5237 with
                                  | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                      ->
                                      let bs =
                                        match b with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5294 =
                                              FStar_Syntax_Syntax.null_binder
                                                t1 in
                                            [uu____5294]
                                        | FStar_Pervasives_Native.Some x ->
                                            let uu____5296 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____5296] in
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
                                        let uu____5309 =
                                          FStar_Syntax_Syntax.as_arg r11 in
                                        let uu____5310 =
                                          let uu____5313 =
                                            FStar_Syntax_Syntax.as_arg t1 in
                                          let uu____5314 =
                                            let uu____5317 =
                                              FStar_Syntax_Syntax.as_arg t2 in
                                            let uu____5318 =
                                              let uu____5321 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wp1 in
                                              let uu____5322 =
                                                let uu____5325 =
                                                  let uu____5326 = mk_lam wp2 in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____5326 in
                                                [uu____5325] in
                                              uu____5321 :: uu____5322 in
                                            uu____5317 :: uu____5318 in
                                          uu____5313 :: uu____5314 in
                                        uu____5309 :: uu____5310 in
                                      let wp =
                                        let uu____5330 =
                                          let uu____5331 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t1; u_t2] env md
                                              md.FStar_Syntax_Syntax.bind_wp in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____5331 wp_args in
                                        uu____5330
                                          FStar_Pervasives_Native.None
                                          t2.FStar_Syntax_Syntax.pos in
                                      mk_comp md u_t2 t2 wp bind_flags)))) in
                  {
                    FStar_Syntax_Syntax.eff_name = joined_eff;
                    FStar_Syntax_Syntax.res_typ =
                      (lc21.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = bind_flags;
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
      | uu____5343 -> g2
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
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____5380 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5380
            then (lc, g0)
            else
              ((let uu____5387 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5387
                then
                  let uu____5388 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      e_for_debug_only in
                  let uu____5389 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5388 uu____5389
                else ());
               (let flags1 =
                  let uu____5394 =
                    let uu____5401 =
                      FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                    if uu____5401
                    then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                    else (false, []) in
                  match uu____5394 with
                  | (maybe_trivial_post,flags1) ->
                      let uu____5421 =
                        FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                          (FStar_List.collect
                             (fun uu___83_5429  ->
                                match uu___83_5429 with
                                | FStar_Syntax_Syntax.RETURN  ->
                                    [FStar_Syntax_Syntax.PARTIAL_RETURN]
                                | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                    [FStar_Syntax_Syntax.PARTIAL_RETURN]
                                | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                    Prims.op_Negation maybe_trivial_post ->
                                    [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                                | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                    when Prims.op_Negation maybe_trivial_post
                                    ->
                                    [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                | uu____5432 -> [])) in
                      FStar_List.append flags1 uu____5421 in
                let strengthen uu____5438 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5446 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5446 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         ((let uu____5451 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5451
                           then
                             let uu____5452 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e_for_debug_only in
                             let uu____5453 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5452 uu____5453
                           else ());
                          (let c1 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                           let uu____5456 = destruct_comp c1 in
                           match uu____5456 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c1.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5472 =
                                   let uu____5473 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5474 =
                                     let uu____5475 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5476 =
                                       let uu____5479 =
                                         let uu____5480 =
                                           let uu____5481 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5481 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5480 in
                                       let uu____5482 =
                                         let uu____5485 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5485] in
                                       uu____5479 :: uu____5482 in
                                     uu____5475 :: uu____5476 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5473
                                     uu____5474 in
                                 uu____5472 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5489 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5489
                                 then
                                   let uu____5490 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5490
                                 else ());
                                (let c2 = mk_comp md u_res_t res_t wp1 flags1 in
                                 c2))))) in
                let uu____5493 =
                  let uu___116_5494 = lc in
                  let uu____5495 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5495;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___116_5494.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = flags1;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5493,
                  (let uu___117_5497 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___117_5497.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___117_5497.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___117_5497.FStar_TypeChecker_Env.implicits)
                   }))))
let maybe_assume_result_eq_pure_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____5509 = FStar_Syntax_Util.is_lcomp_partial_return lc in
             Prims.op_Negation uu____5509) in
        let flags1 =
          if should_return1
          then
            let uu____5515 = FStar_Syntax_Util.is_total_lcomp lc in
            (if uu____5515
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5523 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c) in
          let uu____5529 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
          if uu____5529
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e in
            let uu____5531 =
              let uu____5532 = FStar_Syntax_Util.is_pure_comp c in
              Prims.op_Negation uu____5532 in
            (if uu____5531
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
               let retc2 =
                 let uu___118_5535 = retc1 in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___118_5535.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___118_5535.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___118_5535.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 } in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
             let t = c1.FStar_Syntax_Syntax.result_typ in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1 in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t in
             let xexp = FStar_Syntax_Syntax.bv_to_name x in
             let ret1 =
               let uu____5546 =
                 let uu____5549 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp in
                 FStar_Syntax_Util.comp_set_flags uu____5549
                   [FStar_Syntax_Syntax.PARTIAL_RETURN] in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5546 in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1) in
             let uu____5554 =
               let uu____5555 =
                 let uu____5560 =
                   bind e.FStar_Syntax_Syntax.pos env
                     FStar_Pervasives_Native.None
                     (FStar_Syntax_Util.lcomp_of_comp c2)
                     ((FStar_Pervasives_Native.Some x), eq_ret) in
                 uu____5560.FStar_Syntax_Syntax.comp in
               uu____5555 () in
             FStar_Syntax_Util.comp_set_flags uu____5554 flags1) in
        if Prims.op_Negation should_return1
        then lc
        else
          (let uu___119_5564 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___119_5564.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___119_5564.FStar_Syntax_Syntax.res_typ);
             FStar_Syntax_Syntax.cflags = flags1;
             FStar_Syntax_Syntax.comp = refine1
           })
let maybe_return_e2_and_bind:
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____5584  ->
              match uu____5584 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name in
                    let uu____5596 =
                      ((let uu____5599 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____5599) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____5596
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let fvar_const:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____5609 =
        let uu____5610 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5610 in
      FStar_Syntax_Syntax.fvar uu____5609 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
let bind_cases:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5669  ->
                 match uu____5669 with
                 | (uu____5682,eff_label,uu____5684,uu____5685) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let uu____5694 =
          let uu____5701 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5733  ->
                    match uu____5733 with
                    | (uu____5746,uu____5747,flags1,uu____5749) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___84_5761  ->
                                match uu___84_5761 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5762 -> false)))) in
          if uu____5701
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, []) in
        match uu____5694 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5783 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
              let uu____5785 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5785
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5805 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos in
                   let uu____5806 =
                     let uu____5807 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else in
                     let uu____5808 =
                       let uu____5809 = FStar_Syntax_Syntax.as_arg res_t1 in
                       let uu____5810 =
                         let uu____5813 = FStar_Syntax_Syntax.as_arg g in
                         let uu____5814 =
                           let uu____5817 = FStar_Syntax_Syntax.as_arg wp_t in
                           let uu____5818 =
                             let uu____5821 = FStar_Syntax_Syntax.as_arg wp_e in
                             [uu____5821] in
                           uu____5817 :: uu____5818 in
                         uu____5813 :: uu____5814 in
                       uu____5809 :: uu____5810 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5807 uu____5808 in
                   uu____5806 FStar_Pervasives_Native.None uu____5805 in
                 let default_case =
                   let post_k =
                     let uu____5828 =
                       let uu____5835 = FStar_Syntax_Syntax.null_binder res_t in
                       [uu____5835] in
                     let uu____5836 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5828 uu____5836 in
                   let kwp =
                     let uu____5842 =
                       let uu____5849 =
                         FStar_Syntax_Syntax.null_binder post_k in
                       [uu____5849] in
                     let uu____5850 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5842 uu____5850 in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k in
                   let wp =
                     let uu____5855 =
                       let uu____5856 = FStar_Syntax_Syntax.mk_binder post in
                       [uu____5856] in
                     let uu____5857 =
                       let uu____5858 =
                         let uu____5861 = FStar_TypeChecker_Env.get_range env in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____5861 in
                       let uu____5862 =
                         fvar_const env FStar_Parser_Const.false_lid in
                       FStar_All.pipe_left uu____5858 uu____5862 in
                     FStar_Syntax_Util.abs uu____5855 uu____5857
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL])) in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid in
                   mk_comp md u_res_t res_t wp [] in
                 let maybe_return eff_label_then cthen =
                   let uu____5878 =
                     should_not_inline_whole_match ||
                       (let uu____5880 = is_pure_or_ghost_effect env eff in
                        Prims.op_Negation uu____5880) in
                   if uu____5878 then cthen true else cthen false in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____5912  ->
                        fun celse  ->
                          match uu____5912 with
                          | (g,eff_label,uu____5928,cthen) ->
                              let uu____5938 =
                                let uu____5963 =
                                  let uu____5964 =
                                    let uu____5969 =
                                      maybe_return eff_label cthen in
                                    uu____5969.FStar_Syntax_Syntax.comp in
                                  uu____5964 () in
                                lift_and_destruct env uu____5963 celse in
                              (match uu____5938 with
                               | ((md,uu____5971,uu____5972),(uu____5973,uu____5974,wp_then),
                                  (uu____5976,uu____5977,wp_else)) ->
                                   let uu____5997 =
                                     ifthenelse md res_t g wp_then wp_else in
                                   mk_comp md u_res_t res_t uu____5997 []))
                     lcases default_case in
                 match lcases with
                 | [] -> comp
                 | uu____6010::[] -> comp
                 | uu____6047 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name in
                     let uu____6064 = destruct_comp comp1 in
                     (match uu____6064 with
                      | (uu____6071,uu____6072,wp) ->
                          let wp1 =
                            let uu____6077 =
                              let uu____6078 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp in
                              let uu____6079 =
                                let uu____6080 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____6081 =
                                  let uu____6084 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____6084] in
                                uu____6080 :: uu____6081 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6078
                                uu____6079 in
                            uu____6077 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags)) in
            {
              FStar_Syntax_Syntax.eff_name = eff;
              FStar_Syntax_Syntax.res_typ = res_t;
              FStar_Syntax_Syntax.cflags = bind_cases_flags;
              FStar_Syntax_Syntax.comp = bind_cases
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
          let uu____6111 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6111 with
          | FStar_Pervasives_Native.None  ->
              let uu____6120 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c' in
              let uu____6125 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____6120 uu____6125
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
            let uu____6158 =
              let uu____6159 = FStar_Syntax_Subst.compress t2 in
              uu____6159.FStar_Syntax_Syntax.n in
            match uu____6158 with
            | FStar_Syntax_Syntax.Tm_type uu____6162 -> true
            | uu____6163 -> false in
          let uu____6164 =
            let uu____6165 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6165.FStar_Syntax_Syntax.n in
          match uu____6164 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6173 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6184 =
                  let uu____6185 =
                    let uu____6186 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6186 in
                  (FStar_Pervasives_Native.None, uu____6185) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6184 in
              let e1 =
                let uu____6196 =
                  let uu____6197 =
                    let uu____6198 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6198] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6197 in
                uu____6196 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6203 -> (e, lc)
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
              (let uu____6232 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6232 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6255 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6277 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6277, false)
            else
              (let uu____6283 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6283, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6294) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6303 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ in
                FStar_Errors.raise_error uu____6303 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___120_6317 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___120_6317.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___120_6317.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___120_6317.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6322 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6322 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___121_6330 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___121_6330.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___121_6330.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___121_6330.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___122_6333 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_6333.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_6333.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___122_6333.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6339 =
                     let uu____6340 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6340
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6345 =
                          let uu____6346 = FStar_Syntax_Subst.compress f1 in
                          uu____6346.FStar_Syntax_Syntax.n in
                        match uu____6345 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6351,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6353;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6354;_},uu____6355)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___123_6377 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___123_6377.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___123_6377.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___123_6377.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6378 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6383 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6383
                              then
                                let uu____6384 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6385 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6386 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6387 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6384 uu____6385 uu____6386 uu____6387
                              else ());
                             (let u_t_opt = comp_univ_opt c in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x in
                              let cret = return_value env u_t_opt t xexp in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____6400 =
                                    let uu____6401 =
                                      let uu____6402 =
                                        FStar_Syntax_Syntax.as_arg xexp in
                                      [uu____6402] in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6401 in
                                  uu____6400 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1 in
                              let uu____6406 =
                                let uu____6411 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t) in
                                let uu____6424 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos in
                                let uu____6425 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard) in
                                strengthen_precondition uu____6411 uu____6424
                                  e (FStar_Syntax_Util.lcomp_of_comp cret)
                                  uu____6425 in
                              match uu____6406 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___124_6431 = x in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_6431.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_6431.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    } in
                                  let c1 =
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      (FStar_Syntax_Util.lcomp_of_comp c)
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret) in
                                  let c2 = c1.FStar_Syntax_Syntax.comp () in
                                  ((let uu____6439 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____6439
                                    then
                                      let uu____6440 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2 in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6440
                                    else ());
                                   c2)))) in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___85_6450  ->
                             match uu___85_6450 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6453 -> [])) in
                   let lc1 =
                     let uu___125_6455 = lc in
                     let uu____6456 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6456;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags1;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___126_6458 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___126_6458.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___126_6458.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___126_6458.FStar_TypeChecker_Env.implicits)
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
        let uu____6481 =
          let uu____6482 =
            let uu____6483 =
              let uu____6484 =
                let uu____6485 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6485 in
              [uu____6484] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6483 in
          uu____6482 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6481 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6492 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6492
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6510 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6525 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6554)::(ens,uu____6556)::uu____6557 ->
                    let uu____6586 =
                      let uu____6589 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6589 in
                    let uu____6590 =
                      let uu____6591 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6591 in
                    (uu____6586, uu____6590)
                | uu____6594 ->
                    let uu____6603 =
                      let uu____6608 =
                        let uu____6609 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6609 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6608) in
                    FStar_Errors.raise_error uu____6603
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6625)::uu____6626 ->
                    let uu____6645 =
                      let uu____6650 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6650 in
                    (match uu____6645 with
                     | (us_r,uu____6682) ->
                         let uu____6683 =
                           let uu____6688 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6688 in
                         (match uu____6683 with
                          | (us_e,uu____6720) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6723 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6723
                                  us_r in
                              let as_ens =
                                let uu____6725 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6725
                                  us_e in
                              let req =
                                let uu____6729 =
                                  let uu____6730 =
                                    let uu____6731 =
                                      let uu____6742 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6742] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6731 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6730 in
                                uu____6729 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6760 =
                                  let uu____6761 =
                                    let uu____6762 =
                                      let uu____6773 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6773] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6762 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6761 in
                                uu____6760 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6788 =
                                let uu____6791 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6791 in
                              let uu____6792 =
                                let uu____6793 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6793 in
                              (uu____6788, uu____6792)))
                | uu____6796 -> failwith "Impossible"))
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
      (let uu____6822 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6822
       then
         let uu____6823 = FStar_Syntax_Print.term_to_string tm in
         let uu____6824 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6823 uu____6824
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
        (let uu____6842 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6842
         then
           let uu____6843 = FStar_Syntax_Print.term_to_string tm in
           let uu____6844 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6843
             uu____6844
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6849 =
      let uu____6850 =
        let uu____6851 = FStar_Syntax_Subst.compress t in
        uu____6851.FStar_Syntax_Syntax.n in
      match uu____6850 with
      | FStar_Syntax_Syntax.Tm_app uu____6854 -> false
      | uu____6869 -> true in
    if uu____6849
    then t
    else
      (let uu____6871 = FStar_Syntax_Util.head_and_args t in
       match uu____6871 with
       | (head1,args) ->
           let uu____6908 =
             let uu____6909 =
               let uu____6910 = FStar_Syntax_Subst.compress head1 in
               uu____6910.FStar_Syntax_Syntax.n in
             match uu____6909 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6913 -> false in
           if uu____6908
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6935 ->
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
             let uu____6972 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6972 with
             | (formals,uu____6986) ->
                 let n_implicits =
                   let uu____7004 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7080  ->
                             match uu____7080 with
                             | (uu____7087,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7004 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7218 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7218 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7242 =
                     let uu____7247 =
                       let uu____7248 = FStar_Util.string_of_int n_expected in
                       let uu____7255 = FStar_Syntax_Print.term_to_string e in
                       let uu____7256 = FStar_Util.string_of_int n_available in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7248 uu____7255 uu____7256 in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7247) in
                   let uu____7263 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error uu____7242 uu____7263
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___86_7284 =
             match uu___86_7284 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7314 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7314 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7423) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7466,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7499 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7499 with
                           | (v1,uu____7539,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7556 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7556 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7649 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7649)))
                      | (uu____7676,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7722 =
                      let uu____7749 = inst_n_binders t in
                      aux [] uu____7749 bs1 in
                    (match uu____7722 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7820) -> (e, torig, guard)
                          | (uu____7851,[]) when
                              let uu____7882 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7882 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7883 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7915 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7930 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7938 =
      let uu____7941 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7941
        (FStar_List.map
           (fun u  ->
              let uu____7951 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7951 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7938 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7968 = FStar_Util.set_is_empty x in
      if uu____7968
      then []
      else
        (let s =
           let uu____7975 =
             let uu____7978 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7978 in
           FStar_All.pipe_right uu____7975 FStar_Util.set_elements in
         (let uu____7986 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7986
          then
            let uu____7987 =
              let uu____7988 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7988 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7987
          else ());
         (let r =
            let uu____7995 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7995 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8010 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8010
                     then
                       let uu____8011 =
                         let uu____8012 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8012 in
                       let uu____8013 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8014 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8011 uu____8013 uu____8014
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
        let uu____8036 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8036 FStar_Util.fifo_set_elements in
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
        | ([],uu____8068) -> generalized_univ_names
        | (uu____8075,[]) -> explicit_univ_names
        | uu____8082 ->
            let uu____8091 =
              let uu____8096 =
                let uu____8097 = FStar_Syntax_Print.term_to_string t in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8097 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8096) in
            FStar_Errors.raise_error uu____8091 t.FStar_Syntax_Syntax.pos
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
      (let uu____8114 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8114
       then
         let uu____8115 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8115
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8121 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8121
        then
          let uu____8122 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8122
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
        let uu____8192 =
          let uu____8193 =
            FStar_Util.for_all
              (fun uu____8206  ->
                 match uu____8206 with
                 | (uu____8215,uu____8216,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8193 in
        if uu____8192
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8262 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8262
              then
                let uu____8263 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8263
              else ());
             (let c1 =
                let uu____8266 = FStar_TypeChecker_Env.should_verify env in
                if uu____8266
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
              (let uu____8269 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8269
               then
                 let uu____8270 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8270
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8331 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8331 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8461 =
             match uu____8461 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8527 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8527
                   then
                     let uu____8528 =
                       let uu____8529 =
                         let uu____8532 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8532
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8529
                         (FStar_String.concat ", ") in
                     let uu____8559 =
                       let uu____8560 =
                         let uu____8563 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8563
                           (FStar_List.map
                              (fun uu____8591  ->
                                 match uu____8591 with
                                 | (u,t2) ->
                                     let uu____8598 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8599 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8598 uu____8599)) in
                       FStar_All.pipe_right uu____8560
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8528
                       uu____8559
                   else ());
                  (let univs2 =
                     let uu____8606 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8629  ->
                            match uu____8629 with
                            | (uu____8638,t2) ->
                                let uu____8640 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8640)
                       univs1 uu____8606 in
                   let uvs = gen_uvars uvt in
                   (let uu____8663 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8663
                    then
                      let uu____8664 =
                        let uu____8665 =
                          let uu____8668 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8668
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8665
                          (FStar_String.concat ", ") in
                      let uu____8695 =
                        let uu____8696 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8728  ->
                                  match uu____8728 with
                                  | (u,t2) ->
                                      let uu____8735 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8736 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8735 uu____8736)) in
                        FStar_All.pipe_right uu____8696
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8664
                        uu____8695
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8766 =
             let uu____8799 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8799 in
           match uu____8766 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8917 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8917
                 then ()
                 else
                   (let uu____8919 = lec_hd in
                    match uu____8919 with
                    | (lb1,uu____8927,uu____8928) ->
                        let uu____8929 = lec2 in
                        (match uu____8929 with
                         | (lb2,uu____8937,uu____8938) ->
                             let msg =
                               let uu____8940 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8941 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8940 uu____8941 in
                             let uu____8942 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8942)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9053  ->
                           match uu____9053 with
                           | (u,uu____9061) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9083  ->
                                       match uu____9083 with
                                       | (u',uu____9091) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9096 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9096
                 then ()
                 else
                   (let uu____9098 = lec_hd in
                    match uu____9098 with
                    | (lb1,uu____9106,uu____9107) ->
                        let uu____9108 = lec2 in
                        (match uu____9108 with
                         | (lb2,uu____9116,uu____9117) ->
                             let msg =
                               let uu____9119 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9120 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9119 uu____9120 in
                             let uu____9121 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9121)) in
               let lecs1 =
                 let uu____9131 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9190 = univs_and_uvars_of_lec this_lec in
                        match uu____9190 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9131 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9343 = lec_hd in
                   match uu____9343 with
                   | (lbname,e,c) ->
                       let uu____9353 =
                         let uu____9358 =
                           let uu____9359 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____9360 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____9361 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9359 uu____9360 uu____9361 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9358) in
                       let uu____9362 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____9353 uu____9362 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9392  ->
                         match uu____9392 with
                         | (u,k) ->
                             let uu____9405 = FStar_Syntax_Unionfind.find u in
                             (match uu____9405 with
                              | FStar_Pervasives_Native.Some uu____9414 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9421 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9425 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9425 with
                                   | (bs,kres) ->
                                       ((let uu____9463 =
                                           let uu____9464 =
                                             let uu____9467 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9467 in
                                           uu____9464.FStar_Syntax_Syntax.n in
                                         match uu____9463 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9468 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9472 =
                                               let uu____9473 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9473 in
                                             if uu____9472
                                             then fail kres
                                             else ()
                                         | uu____9475 -> fail kres);
                                        (let a =
                                           let uu____9477 =
                                             let uu____9480 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9480 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9477 kres in
                                         let t =
                                           let uu____9484 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9484
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
                      (fun uu____9603  ->
                         match uu____9603 with
                         | (lbname,e,c) ->
                             let uu____9649 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9718 ->
                                   let uu____9733 = (e, c) in
                                   (match uu____9733 with
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
                                                (fun uu____9770  ->
                                                   match uu____9770 with
                                                   | (x,uu____9778) ->
                                                       let uu____9783 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9783)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9793 =
                                                let uu____9794 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9794 in
                                              if uu____9793
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
                                          let uu____9802 =
                                            let uu____9803 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9803.FStar_Syntax_Syntax.n in
                                          match uu____9802 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9826 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9826 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9841 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9843 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9843, gen_tvars)) in
                             (match uu____9649 with
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
        (let uu____9989 = Obj.magic () in ());
        (let uu____9991 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9991
         then
           let uu____9992 =
             let uu____9993 =
               FStar_List.map
                 (fun uu____10006  ->
                    match uu____10006 with
                    | (lb,uu____10014,uu____10015) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9993 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9992
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10036  ->
                match uu____10036 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10065 = gen env is_rec lecs in
           match uu____10065 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10164  ->
                       match uu____10164 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10226 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10226
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10270  ->
                           match uu____10270 with
                           | (l,us,e,c,gvs) ->
                               let uu____10304 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10305 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10306 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10307 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10308 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10304 uu____10305 uu____10306
                                 uu____10307 uu____10308))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10349  ->
                match uu____10349 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10393 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10393, t, c, gvs)) univnames_lecs
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
              (let uu____10436 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10436 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10442 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10442) in
          let is_var e1 =
            let uu____10449 =
              let uu____10450 = FStar_Syntax_Subst.compress e1 in
              uu____10450.FStar_Syntax_Syntax.n in
            match uu____10449 with
            | FStar_Syntax_Syntax.Tm_name uu____10453 -> true
            | uu____10454 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___127_10470 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___127_10470.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___127_10470.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10471 -> e2 in
          let env2 =
            let uu___128_10473 = env1 in
            let uu____10474 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___128_10473.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___128_10473.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___128_10473.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___128_10473.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___128_10473.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___128_10473.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___128_10473.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___128_10473.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___128_10473.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___128_10473.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___128_10473.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___128_10473.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___128_10473.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___128_10473.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___128_10473.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10474;
              FStar_TypeChecker_Env.is_iface =
                (uu___128_10473.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___128_10473.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___128_10473.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___128_10473.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___128_10473.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___128_10473.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___128_10473.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___128_10473.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___128_10473.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___128_10473.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___128_10473.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___128_10473.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___128_10473.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___128_10473.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___128_10473.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___128_10473.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___128_10473.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___128_10473.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10475 = check env2 t1 t2 in
          match uu____10475 with
          | FStar_Pervasives_Native.None  ->
              let uu____10482 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____10487 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____10482 uu____10487
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10494 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10494
                then
                  let uu____10495 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10495
                else ());
               (let uu____10497 = decorate e t2 in (uu____10497, g)))
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
        let uu____10525 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10525
        then
          let uu____10530 = discharge g1 in
          let uu____10531 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10530, uu____10531)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10544 =
               let uu____10545 =
                 let uu____10546 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10546 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10545
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10544
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10548 = destruct_comp c1 in
           match uu____10548 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10565 = FStar_TypeChecker_Env.get_range env in
                 let uu____10566 =
                   let uu____10567 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10568 =
                     let uu____10569 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10570 =
                       let uu____10573 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10573] in
                     uu____10569 :: uu____10570 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10567 uu____10568 in
                 uu____10566 FStar_Pervasives_Native.None uu____10565 in
               ((let uu____10577 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10577
                 then
                   let uu____10578 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10578
                 else ());
                (let g2 =
                   let uu____10581 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10581 in
                 let uu____10582 = discharge g2 in
                 let uu____10583 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10582, uu____10583))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___87_10607 =
        match uu___87_10607 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10615)::[] -> f fst1
        | uu____10632 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10637 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10637
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10646 =
          let uu____10649 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10649 in
        FStar_All.pipe_right uu____10646
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10660 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10660
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___88_10674 =
        match uu___88_10674 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10682)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10701)::[] ->
            let uu____10730 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10730
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10735 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10745 =
          let uu____10752 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10752) in
        let uu____10757 =
          let uu____10766 =
            let uu____10773 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10773) in
          let uu____10778 =
            let uu____10787 =
              let uu____10794 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10794) in
            let uu____10799 =
              let uu____10808 =
                let uu____10815 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10815) in
              let uu____10820 =
                let uu____10829 =
                  let uu____10836 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10836) in
                [uu____10829; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10808 :: uu____10820 in
            uu____10787 :: uu____10799 in
          uu____10766 :: uu____10778 in
        uu____10745 :: uu____10757 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10887 =
            FStar_Util.find_map table
              (fun uu____10900  ->
                 match uu____10900 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10917 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10917
                     else FStar_Pervasives_Native.None) in
          (match uu____10887 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10920 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10924 =
      let uu____10925 = FStar_Syntax_Util.un_uinst l in
      uu____10925.FStar_Syntax_Syntax.n in
    match uu____10924 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10929 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10953)::uu____10954 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10965 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10972,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10973))::uu____10974 -> bs
      | uu____10991 ->
          let uu____10992 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10992 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10996 =
                 let uu____10997 = FStar_Syntax_Subst.compress t in
                 uu____10997.FStar_Syntax_Syntax.n in
               (match uu____10996 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11001) ->
                    let uu____11018 =
                      FStar_Util.prefix_until
                        (fun uu___89_11058  ->
                           match uu___89_11058 with
                           | (uu____11065,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11066)) ->
                               false
                           | uu____11069 -> true) bs' in
                    (match uu____11018 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11104,uu____11105) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11177,uu____11178) ->
                         let uu____11251 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11269  ->
                                   match uu____11269 with
                                   | (x,uu____11277) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11251
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11324  ->
                                     match uu____11324 with
                                     | (x,i) ->
                                         let uu____11343 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11343, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11353 -> bs))
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
          let uu____11385 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11385
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
        (let uu____11408 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11408
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11410 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11410))
         else ());
        (let fv =
           let uu____11413 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11413
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
         let uu____11421 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___129_11427 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___129_11427.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___129_11427.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___129_11427.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___129_11427.FStar_Syntax_Syntax.sigattrs)
           }), uu____11421))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___90_11437 =
        match uu___90_11437 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11438 -> false in
      let reducibility uu___91_11442 =
        match uu___91_11442 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11443 -> false in
      let assumption uu___92_11447 =
        match uu___92_11447 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11448 -> false in
      let reification uu___93_11452 =
        match uu___93_11452 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11453 -> true
        | uu____11454 -> false in
      let inferred uu___94_11458 =
        match uu___94_11458 with
        | FStar_Syntax_Syntax.Discriminator uu____11459 -> true
        | FStar_Syntax_Syntax.Projector uu____11460 -> true
        | FStar_Syntax_Syntax.RecordType uu____11465 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11474 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11483 -> false in
      let has_eq uu___95_11487 =
        match uu___95_11487 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11488 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11548 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11553 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11557 =
        let uu____11558 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___96_11562  ->
                  match uu___96_11562 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11563 -> false)) in
        FStar_All.pipe_right uu____11558 Prims.op_Negation in
      if uu____11557
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11576 =
            let uu____11581 =
              let uu____11582 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11582 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11581) in
          FStar_Errors.raise_error uu____11576 r in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11590 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11594 =
            let uu____11595 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11595 in
          if uu____11594 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11600),uu____11601) ->
              ((let uu____11617 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11617
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11621 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11621
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11627 ->
              let uu____11636 =
                let uu____11637 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11637 in
              if uu____11636 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11643 ->
              let uu____11650 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11650 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11654 ->
              let uu____11661 =
                let uu____11662 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11662 in
              if uu____11661 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11668 ->
              let uu____11669 =
                let uu____11670 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11670 in
              if uu____11669 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11676 ->
              let uu____11677 =
                let uu____11678 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11678 in
              if uu____11677 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11684 ->
              let uu____11697 =
                let uu____11698 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11698 in
              if uu____11697 then err'1 () else ()
          | uu____11704 -> ()))
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
                          let uu____11767 =
                            let uu____11770 =
                              let uu____11771 =
                                let uu____11778 =
                                  let uu____11779 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11779 in
                                (uu____11778, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11771 in
                            FStar_Syntax_Syntax.mk uu____11770 in
                          uu____11767 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11820  ->
                                  match uu____11820 with
                                  | (x,imp) ->
                                      let uu____11831 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11831, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11833 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11833 in
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
                             let uu____11842 =
                               let uu____11843 =
                                 let uu____11844 =
                                   let uu____11845 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11846 =
                                     let uu____11847 =
                                       let uu____11848 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11848 in
                                     [uu____11847] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11845
                                     uu____11846 in
                                 uu____11844 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11843 in
                             FStar_Syntax_Util.refine x uu____11842 in
                           let uu____11851 =
                             let uu___130_11852 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___130_11852.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___130_11852.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11851) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11867 =
                          FStar_List.map
                            (fun uu____11889  ->
                               match uu____11889 with
                               | (x,uu____11901) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11867 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11950  ->
                                match uu____11950 with
                                | (x,uu____11962) ->
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
                             (let uu____11976 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11976)
                               ||
                               (let uu____11978 =
                                  let uu____11979 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11979.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11978) in
                           let quals =
                             let uu____11983 =
                               let uu____11986 =
                                 let uu____11989 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11989
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11993 =
                                 FStar_List.filter
                                   (fun uu___97_11997  ->
                                      match uu___97_11997 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11998 -> false) iquals in
                               FStar_List.append uu____11986 uu____11993 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11983 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12019 =
                                 let uu____12020 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12020 in
                               FStar_Syntax_Syntax.mk_Total uu____12019 in
                             let uu____12021 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12021 in
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
                           (let uu____12024 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12024
                            then
                              let uu____12025 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12025
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
                                             fun uu____12078  ->
                                               match uu____12078 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12102 =
                                                       let uu____12105 =
                                                         let uu____12106 =
                                                           let uu____12113 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12113,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12106 in
                                                       pos uu____12105 in
                                                     (uu____12102, b)
                                                   else
                                                     (let uu____12117 =
                                                        let uu____12120 =
                                                          let uu____12121 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12121 in
                                                        pos uu____12120 in
                                                      (uu____12117, b)))) in
                                   let pat_true =
                                     let uu____12139 =
                                       let uu____12142 =
                                         let uu____12143 =
                                           let uu____12156 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12156, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12143 in
                                       pos uu____12142 in
                                     (uu____12139,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12190 =
                                       let uu____12193 =
                                         let uu____12194 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12194 in
                                       pos uu____12193 in
                                     (uu____12190,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12206 =
                                     let uu____12209 =
                                       let uu____12210 =
                                         let uu____12233 =
                                           let uu____12236 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12237 =
                                             let uu____12240 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12240] in
                                           uu____12236 :: uu____12237 in
                                         (arg_exp, uu____12233) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12210 in
                                     FStar_Syntax_Syntax.mk uu____12209 in
                                   uu____12206 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12247 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12247
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
                                let uu____12255 =
                                  let uu____12260 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12260 in
                                let uu____12261 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12255;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12261
                                } in
                              let impl =
                                let uu____12265 =
                                  let uu____12266 =
                                    let uu____12273 =
                                      let uu____12276 =
                                        let uu____12277 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12277
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12276] in
                                    ((false, [lb]), uu____12273) in
                                  FStar_Syntax_Syntax.Sig_let uu____12266 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12265;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12295 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12295
                               then
                                 let uu____12296 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12296
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
                                fun uu____12338  ->
                                  match uu____12338 with
                                  | (a,uu____12344) ->
                                      let uu____12345 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12345 with
                                       | (field_name,uu____12351) ->
                                           let field_proj_tm =
                                             let uu____12353 =
                                               let uu____12354 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12354 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12353 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12371 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12403  ->
                                    match uu____12403 with
                                    | (x,uu____12411) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12413 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12413 with
                                         | (field_name,uu____12421) ->
                                             let t =
                                               let uu____12423 =
                                                 let uu____12424 =
                                                   let uu____12427 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12427 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12424 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12423 in
                                             let only_decl =
                                               (let uu____12431 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12431)
                                                 ||
                                                 (let uu____12433 =
                                                    let uu____12434 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12434.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12433) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12448 =
                                                   FStar_List.filter
                                                     (fun uu___98_12452  ->
                                                        match uu___98_12452
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12453 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12448
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___99_12466  ->
                                                         match uu___99_12466
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12467 ->
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
                                             ((let uu____12486 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12486
                                               then
                                                 let uu____12487 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12487
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
                                                           fun uu____12535 
                                                             ->
                                                             match uu____12535
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12559
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12559,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12575
                                                                    =
                                                                    let uu____12578
                                                                    =
                                                                    let uu____12579
                                                                    =
                                                                    let uu____12586
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12586,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12579 in
                                                                    pos
                                                                    uu____12578 in
                                                                    (uu____12575,
                                                                    b))
                                                                   else
                                                                    (let uu____12590
                                                                    =
                                                                    let uu____12593
                                                                    =
                                                                    let uu____12594
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12594 in
                                                                    pos
                                                                    uu____12593 in
                                                                    (uu____12590,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12610 =
                                                     let uu____12613 =
                                                       let uu____12614 =
                                                         let uu____12627 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12627,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12614 in
                                                     pos uu____12613 in
                                                   let uu____12636 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12610,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12636) in
                                                 let body =
                                                   let uu____12648 =
                                                     let uu____12651 =
                                                       let uu____12652 =
                                                         let uu____12675 =
                                                           let uu____12678 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12678] in
                                                         (arg_exp,
                                                           uu____12675) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12652 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12651 in
                                                   uu____12648
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12686 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12686
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
                                                   let uu____12693 =
                                                     let uu____12698 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12698 in
                                                   let uu____12699 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12693;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12699
                                                   } in
                                                 let impl =
                                                   let uu____12703 =
                                                     let uu____12704 =
                                                       let uu____12711 =
                                                         let uu____12714 =
                                                           let uu____12715 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12715
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12714] in
                                                       ((false, [lb]),
                                                         uu____12711) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12704 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12703;
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
                                                 (let uu____12733 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12733
                                                  then
                                                    let uu____12734 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12734
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12371 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12774) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12779 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12779 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12801 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12801 with
                    | (formals,uu____12817) ->
                        let uu____12834 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12866 =
                                   let uu____12867 =
                                     let uu____12868 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12868 in
                                   FStar_Ident.lid_equals typ_lid uu____12867 in
                                 if uu____12866
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12887,uvs',tps,typ0,uu____12891,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12910 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None) in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng in
                        (match uu____12834 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12983 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12983 with
                              | (indices,uu____12999) ->
                                  let refine_domain =
                                    let uu____13017 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___100_13022  ->
                                              match uu___100_13022 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13023 -> true
                                              | uu____13032 -> false)) in
                                    if uu____13017
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___101_13040 =
                                      match uu___101_13040 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13043,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13055 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13056 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13056 with
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
                                    let uu____13067 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13067 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13132  ->
                                               fun uu____13133  ->
                                                 match (uu____13132,
                                                         uu____13133)
                                                 with
                                                 | ((x,uu____13151),(x',uu____13153))
                                                     ->
                                                     let uu____13162 =
                                                       let uu____13169 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13169) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13162) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13170 -> []