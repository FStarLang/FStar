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
                        let subst_c2 e1opt1 reason =
                          match (e1opt1, b) with
                          | (FStar_Pervasives_Native.Some
                             e,FStar_Pervasives_Native.Some x) ->
                              let uu____4979 =
                                let uu____4984 =
                                  FStar_Syntax_Subst.subst_comp
                                    [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                (uu____4984, reason) in
                              FStar_Util.Inl uu____4979
                          | uu____4991 -> aux () in
                        let try_simplify uu____5015 =
                          let rec maybe_close t x c =
                            let uu____5026 =
                              let uu____5027 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____5027.FStar_Syntax_Syntax.n in
                            match uu____5026 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____5031) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____5037 -> c in
                          let uu____5038 =
                            let uu____5039 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____5039 in
                          if uu____5038
                          then
                            let uu____5052 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____5052
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____5072 =
                                  FStar_TypeChecker_Env.get_range env in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                    "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                  uu____5072))
                          else
                            (let uu____5084 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____5084
                             then subst_c2 e1opt "both total"
                             else
                               (let uu____5096 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____5096
                                then
                                  let uu____5107 =
                                    let uu____5112 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____5112, "both gtot") in
                                  FStar_Util.Inl uu____5107
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____5138 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____5140 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____5140) in
                                       if uu____5138
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___115_5153 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___115_5153.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___115_5153.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____5154 =
                                           let uu____5159 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____5159, "c1 Tot") in
                                         FStar_Util.Inl uu____5154
                                       else aux ()
                                   | uu____5165 -> aux ()))) in
                        let uu____5174 = try_simplify () in
                        match uu____5174 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____5198 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____5198
                              then
                                let uu____5199 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____5200 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____5201 =
                                  FStar_Syntax_Print.comp_to_string c in
                                let uu____5202 =
                                  FStar_Syntax_Print.lid_to_string joined_eff in
                                FStar_Util.print5
                                  "Simplified (because %s) bind c1: %s\n\nc2: %s\n\nto c: %s\n\nWith effect lid: %s\n\n"
                                  reason uu____5199 uu____5200 uu____5201
                                  uu____5202
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____5212 = destruct_comp c1_typ in
                            (match uu____5212 with
                             | (u_res_t1,res_t1,uu____5221) ->
                                 let c21 =
                                   let uu____5223 =
                                     (FStar_Option.isSome b) &&
                                       (should_return env e1opt lc11) in
                                   if uu____5223
                                   then
                                     let e1 = FStar_Option.get e1opt in
                                     let x = FStar_Option.get b in
                                     let uu____5226 =
                                       FStar_Syntax_Util.is_partial_return c1 in
                                     (if uu____5226
                                      then
                                        FStar_Syntax_Subst.subst_comp
                                          [FStar_Syntax_Syntax.NT (x, e1)] c2
                                      else
                                        (let uu____5228 =
                                           (lcomp_has_trivial_postcondition
                                              lc11)
                                             &&
                                             (let uu____5230 =
                                                FStar_TypeChecker_Env.try_lookup_lid
                                                  env
                                                  FStar_Parser_Const.with_type_lid in
                                              FStar_Option.isSome uu____5230) in
                                         if uu____5228
                                         then
                                           let e1' =
                                             FStar_Syntax_Util.mk_with_type
                                               u_res_t1 res_t1 e1 in
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e1')]
                                             c2
                                         else
                                           (let c21 =
                                              FStar_Syntax_Subst.subst_comp
                                                [FStar_Syntax_Syntax.NT
                                                   (x, e1)] c2 in
                                            let x_eq_e =
                                              let uu____5257 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              FStar_Syntax_Util.mk_eq2
                                                u_res_t1 res_t1 e1 uu____5257 in
                                            weaken_comp env c21 x_eq_e)))
                                   else c2 in
                                 let uu____5259 =
                                   lift_and_destruct env c1 c21 in
                                 (match uu____5259 with
                                  | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                      ->
                                      let bs =
                                        match b with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5316 =
                                              FStar_Syntax_Syntax.null_binder
                                                t1 in
                                            [uu____5316]
                                        | FStar_Pervasives_Native.Some x ->
                                            let uu____5318 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____5318] in
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
                                        let uu____5331 =
                                          FStar_Syntax_Syntax.as_arg r11 in
                                        let uu____5332 =
                                          let uu____5335 =
                                            FStar_Syntax_Syntax.as_arg t1 in
                                          let uu____5336 =
                                            let uu____5339 =
                                              FStar_Syntax_Syntax.as_arg t2 in
                                            let uu____5340 =
                                              let uu____5343 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wp1 in
                                              let uu____5344 =
                                                let uu____5347 =
                                                  let uu____5348 = mk_lam wp2 in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____5348 in
                                                [uu____5347] in
                                              uu____5343 :: uu____5344 in
                                            uu____5339 :: uu____5340 in
                                          uu____5335 :: uu____5336 in
                                        uu____5331 :: uu____5332 in
                                      let wp =
                                        let uu____5352 =
                                          let uu____5353 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t1; u_t2] env md
                                              md.FStar_Syntax_Syntax.bind_wp in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____5353 wp_args in
                                        uu____5352
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
      | uu____5365 -> g2
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
            let uu____5402 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5402
            then (lc, g0)
            else
              ((let uu____5409 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5409
                then
                  let uu____5410 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      e_for_debug_only in
                  let uu____5411 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5410 uu____5411
                else ());
               (let flags1 =
                  let uu____5416 =
                    let uu____5423 =
                      FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                    if uu____5423
                    then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                    else (false, []) in
                  match uu____5416 with
                  | (maybe_trivial_post,flags1) ->
                      let uu____5443 =
                        FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                          (FStar_List.collect
                             (fun uu___83_5451  ->
                                match uu___83_5451 with
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
                                | uu____5454 -> [])) in
                      FStar_List.append flags1 uu____5443 in
                let strengthen uu____5460 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5468 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5468 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         ((let uu____5473 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5473
                           then
                             let uu____5474 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e_for_debug_only in
                             let uu____5475 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5474 uu____5475
                           else ());
                          (let c1 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                           let uu____5478 = destruct_comp c1 in
                           match uu____5478 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c1.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5494 =
                                   let uu____5495 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5496 =
                                     let uu____5497 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5498 =
                                       let uu____5501 =
                                         let uu____5502 =
                                           let uu____5503 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5503 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5502 in
                                       let uu____5504 =
                                         let uu____5507 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5507] in
                                       uu____5501 :: uu____5504 in
                                     uu____5497 :: uu____5498 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5495
                                     uu____5496 in
                                 uu____5494 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5511 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5511
                                 then
                                   let uu____5512 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5512
                                 else ());
                                (let c2 = mk_comp md u_res_t res_t wp1 flags1 in
                                 c2))))) in
                let uu____5515 =
                  let uu___116_5516 = lc in
                  let uu____5517 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5517;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___116_5516.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = flags1;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5515,
                  (let uu___117_5519 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___117_5519.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___117_5519.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___117_5519.FStar_TypeChecker_Env.implicits)
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
            (let uu____5531 = FStar_Syntax_Util.is_lcomp_partial_return lc in
             Prims.op_Negation uu____5531) in
        let flags1 =
          if should_return1
          then
            let uu____5537 = FStar_Syntax_Util.is_total_lcomp lc in
            (if uu____5537
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5545 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c) in
          let uu____5551 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
          if uu____5551
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e in
            let uu____5553 =
              let uu____5554 = FStar_Syntax_Util.is_pure_comp c in
              Prims.op_Negation uu____5554 in
            (if uu____5553
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
               let retc2 =
                 let uu___118_5557 = retc1 in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___118_5557.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___118_5557.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___118_5557.FStar_Syntax_Syntax.effect_args);
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
               let uu____5568 =
                 let uu____5571 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp in
                 FStar_Syntax_Util.comp_set_flags uu____5571
                   [FStar_Syntax_Syntax.PARTIAL_RETURN] in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5568 in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1) in
             let uu____5576 =
               let uu____5577 =
                 let uu____5582 =
                   bind e.FStar_Syntax_Syntax.pos env
                     FStar_Pervasives_Native.None
                     (FStar_Syntax_Util.lcomp_of_comp c2)
                     ((FStar_Pervasives_Native.Some x), eq_ret) in
                 uu____5582.FStar_Syntax_Syntax.comp in
               uu____5577 () in
             FStar_Syntax_Util.comp_set_flags uu____5576 flags1) in
        if Prims.op_Negation should_return1
        then lc
        else
          (let uu___119_5586 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___119_5586.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___119_5586.FStar_Syntax_Syntax.res_typ);
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
            fun uu____5606  ->
              match uu____5606 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name in
                    let uu____5618 =
                      ((let uu____5621 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____5621) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____5618
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let fvar_const:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____5631 =
        let uu____5632 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5632 in
      FStar_Syntax_Syntax.fvar uu____5631 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5691  ->
                 match uu____5691 with
                 | (uu____5704,eff_label,uu____5706,uu____5707) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let uu____5716 =
          let uu____5723 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5755  ->
                    match uu____5755 with
                    | (uu____5768,uu____5769,flags1,uu____5771) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___84_5783  ->
                                match uu___84_5783 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5784 -> false)))) in
          if uu____5723
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, []) in
        match uu____5716 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5805 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
              let uu____5807 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5807
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5827 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos in
                   let uu____5828 =
                     let uu____5829 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else in
                     let uu____5830 =
                       let uu____5831 = FStar_Syntax_Syntax.as_arg res_t1 in
                       let uu____5832 =
                         let uu____5835 = FStar_Syntax_Syntax.as_arg g in
                         let uu____5836 =
                           let uu____5839 = FStar_Syntax_Syntax.as_arg wp_t in
                           let uu____5840 =
                             let uu____5843 = FStar_Syntax_Syntax.as_arg wp_e in
                             [uu____5843] in
                           uu____5839 :: uu____5840 in
                         uu____5835 :: uu____5836 in
                       uu____5831 :: uu____5832 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5829 uu____5830 in
                   uu____5828 FStar_Pervasives_Native.None uu____5827 in
                 let default_case =
                   let post_k =
                     let uu____5850 =
                       let uu____5857 = FStar_Syntax_Syntax.null_binder res_t in
                       [uu____5857] in
                     let uu____5858 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5850 uu____5858 in
                   let kwp =
                     let uu____5864 =
                       let uu____5871 =
                         FStar_Syntax_Syntax.null_binder post_k in
                       [uu____5871] in
                     let uu____5872 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5864 uu____5872 in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k in
                   let wp =
                     let uu____5877 =
                       let uu____5878 = FStar_Syntax_Syntax.mk_binder post in
                       [uu____5878] in
                     let uu____5879 =
                       let uu____5880 =
                         let uu____5883 = FStar_TypeChecker_Env.get_range env in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____5883 in
                       let uu____5884 =
                         fvar_const env FStar_Parser_Const.false_lid in
                       FStar_All.pipe_left uu____5880 uu____5884 in
                     FStar_Syntax_Util.abs uu____5877 uu____5879
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
                   let uu____5900 =
                     should_not_inline_whole_match ||
                       (let uu____5902 = is_pure_or_ghost_effect env eff in
                        Prims.op_Negation uu____5902) in
                   if uu____5900 then cthen true else cthen false in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____5934  ->
                        fun celse  ->
                          match uu____5934 with
                          | (g,eff_label,uu____5950,cthen) ->
                              let uu____5960 =
                                let uu____5985 =
                                  let uu____5986 =
                                    let uu____5991 =
                                      maybe_return eff_label cthen in
                                    uu____5991.FStar_Syntax_Syntax.comp in
                                  uu____5986 () in
                                lift_and_destruct env uu____5985 celse in
                              (match uu____5960 with
                               | ((md,uu____5993,uu____5994),(uu____5995,uu____5996,wp_then),
                                  (uu____5998,uu____5999,wp_else)) ->
                                   let uu____6019 =
                                     ifthenelse md res_t g wp_then wp_else in
                                   mk_comp md u_res_t res_t uu____6019 []))
                     lcases default_case in
                 match lcases with
                 | [] -> comp
                 | uu____6032::[] -> comp
                 | uu____6069 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name in
                     let uu____6086 = destruct_comp comp1 in
                     (match uu____6086 with
                      | (uu____6093,uu____6094,wp) ->
                          let wp1 =
                            let uu____6099 =
                              let uu____6100 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp in
                              let uu____6101 =
                                let uu____6102 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____6103 =
                                  let uu____6106 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____6106] in
                                uu____6102 :: uu____6103 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6100
                                uu____6101 in
                            uu____6099 FStar_Pervasives_Native.None
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
          let uu____6133 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6133 with
          | FStar_Pervasives_Native.None  ->
              let uu____6142 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c' in
              let uu____6147 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____6142 uu____6147
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
            let uu____6180 =
              let uu____6181 = FStar_Syntax_Subst.compress t2 in
              uu____6181.FStar_Syntax_Syntax.n in
            match uu____6180 with
            | FStar_Syntax_Syntax.Tm_type uu____6184 -> true
            | uu____6185 -> false in
          let uu____6186 =
            let uu____6187 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6187.FStar_Syntax_Syntax.n in
          match uu____6186 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6195 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6206 =
                  let uu____6207 =
                    let uu____6208 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6208 in
                  (FStar_Pervasives_Native.None, uu____6207) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6206 in
              let e1 =
                let uu____6218 =
                  let uu____6219 =
                    let uu____6220 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6220] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6219 in
                uu____6218 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6225 -> (e, lc)
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
              (let uu____6254 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6254 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6277 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6299 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6299, false)
            else
              (let uu____6305 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6305, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6316) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6325 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ in
                FStar_Errors.raise_error uu____6325 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___120_6339 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___120_6339.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___120_6339.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___120_6339.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6344 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6344 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___121_6352 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___121_6352.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___121_6352.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___121_6352.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___122_6355 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_6355.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_6355.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___122_6355.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6361 =
                     let uu____6362 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6362
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6367 =
                          let uu____6368 = FStar_Syntax_Subst.compress f1 in
                          uu____6368.FStar_Syntax_Syntax.n in
                        match uu____6367 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6373,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6375;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6376;_},uu____6377)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___123_6399 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___123_6399.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___123_6399.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___123_6399.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6400 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6405 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6405
                              then
                                let uu____6406 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6407 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6408 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6409 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6406 uu____6407 uu____6408 uu____6409
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
                                  let uu____6422 =
                                    let uu____6423 =
                                      let uu____6424 =
                                        FStar_Syntax_Syntax.as_arg xexp in
                                      [uu____6424] in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6423 in
                                  uu____6422 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1 in
                              let uu____6428 =
                                let uu____6433 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t) in
                                let uu____6446 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos in
                                let uu____6447 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard) in
                                strengthen_precondition uu____6433 uu____6446
                                  e (FStar_Syntax_Util.lcomp_of_comp cret)
                                  uu____6447 in
                              match uu____6428 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___124_6453 = x in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___124_6453.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___124_6453.FStar_Syntax_Syntax.index);
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
                                  ((let uu____6461 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____6461
                                    then
                                      let uu____6462 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2 in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6462
                                    else ());
                                   c2)))) in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___85_6472  ->
                             match uu___85_6472 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6475 -> [])) in
                   let lc1 =
                     let uu___125_6477 = lc in
                     let uu____6478 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6478;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags1;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___126_6480 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___126_6480.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___126_6480.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___126_6480.FStar_TypeChecker_Env.implicits)
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
        let uu____6503 =
          let uu____6504 =
            let uu____6505 =
              let uu____6506 =
                let uu____6507 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6507 in
              [uu____6506] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6505 in
          uu____6504 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6503 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6514 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6514
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6532 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6547 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6576)::(ens,uu____6578)::uu____6579 ->
                    let uu____6608 =
                      let uu____6611 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6611 in
                    let uu____6612 =
                      let uu____6613 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6613 in
                    (uu____6608, uu____6612)
                | uu____6616 ->
                    let uu____6625 =
                      let uu____6630 =
                        let uu____6631 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6631 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6630) in
                    FStar_Errors.raise_error uu____6625
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6647)::uu____6648 ->
                    let uu____6667 =
                      let uu____6672 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6672 in
                    (match uu____6667 with
                     | (us_r,uu____6704) ->
                         let uu____6705 =
                           let uu____6710 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6710 in
                         (match uu____6705 with
                          | (us_e,uu____6742) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6745 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6745
                                  us_r in
                              let as_ens =
                                let uu____6747 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6747
                                  us_e in
                              let req =
                                let uu____6751 =
                                  let uu____6752 =
                                    let uu____6753 =
                                      let uu____6764 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6764] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6753 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6752 in
                                uu____6751 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6782 =
                                  let uu____6783 =
                                    let uu____6784 =
                                      let uu____6795 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6795] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6784 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6783 in
                                uu____6782 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6810 =
                                let uu____6813 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6813 in
                              let uu____6814 =
                                let uu____6815 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6815 in
                              (uu____6810, uu____6814)))
                | uu____6818 -> failwith "Impossible"))
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
      (let uu____6844 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6844
       then
         let uu____6845 = FStar_Syntax_Print.term_to_string tm in
         let uu____6846 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6845 uu____6846
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
        (let uu____6864 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6864
         then
           let uu____6865 = FStar_Syntax_Print.term_to_string tm in
           let uu____6866 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6865
             uu____6866
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6871 =
      let uu____6872 =
        let uu____6873 = FStar_Syntax_Subst.compress t in
        uu____6873.FStar_Syntax_Syntax.n in
      match uu____6872 with
      | FStar_Syntax_Syntax.Tm_app uu____6876 -> false
      | uu____6891 -> true in
    if uu____6871
    then t
    else
      (let uu____6893 = FStar_Syntax_Util.head_and_args t in
       match uu____6893 with
       | (head1,args) ->
           let uu____6930 =
             let uu____6931 =
               let uu____6932 = FStar_Syntax_Subst.compress head1 in
               uu____6932.FStar_Syntax_Syntax.n in
             match uu____6931 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6935 -> false in
           if uu____6930
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6957 ->
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
             let uu____6994 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6994 with
             | (formals,uu____7008) ->
                 let n_implicits =
                   let uu____7026 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7102  ->
                             match uu____7102 with
                             | (uu____7109,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7026 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7240 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7240 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7264 =
                     let uu____7269 =
                       let uu____7270 = FStar_Util.string_of_int n_expected in
                       let uu____7277 = FStar_Syntax_Print.term_to_string e in
                       let uu____7278 = FStar_Util.string_of_int n_available in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7270 uu____7277 uu____7278 in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7269) in
                   let uu____7285 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error uu____7264 uu____7285
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___86_7306 =
             match uu___86_7306 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7336 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7336 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7445) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7488,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7521 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7521 with
                           | (v1,uu____7561,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7578 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7578 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7671 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7671)))
                      | (uu____7698,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7744 =
                      let uu____7771 = inst_n_binders t in
                      aux [] uu____7771 bs1 in
                    (match uu____7744 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7842) -> (e, torig, guard)
                          | (uu____7873,[]) when
                              let uu____7904 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7904 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7905 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7937 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7952 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7960 =
      let uu____7963 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7963
        (FStar_List.map
           (fun u  ->
              let uu____7973 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7973 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7960 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7990 = FStar_Util.set_is_empty x in
      if uu____7990
      then []
      else
        (let s =
           let uu____7997 =
             let uu____8000 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____8000 in
           FStar_All.pipe_right uu____7997 FStar_Util.set_elements in
         (let uu____8008 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____8008
          then
            let uu____8009 =
              let uu____8010 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8010 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8009
          else ());
         (let r =
            let uu____8017 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8017 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8032 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8032
                     then
                       let uu____8033 =
                         let uu____8034 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8034 in
                       let uu____8035 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8036 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8033 uu____8035 uu____8036
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
        let uu____8058 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8058 FStar_Util.fifo_set_elements in
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
        | ([],uu____8090) -> generalized_univ_names
        | (uu____8097,[]) -> explicit_univ_names
        | uu____8104 ->
            let uu____8113 =
              let uu____8118 =
                let uu____8119 = FStar_Syntax_Print.term_to_string t in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8119 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8118) in
            FStar_Errors.raise_error uu____8113 t.FStar_Syntax_Syntax.pos
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
      (let uu____8136 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8136
       then
         let uu____8137 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8137
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8143 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8143
        then
          let uu____8144 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8144
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
        let uu____8214 =
          let uu____8215 =
            FStar_Util.for_all
              (fun uu____8228  ->
                 match uu____8228 with
                 | (uu____8237,uu____8238,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8215 in
        if uu____8214
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8284 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8284
              then
                let uu____8285 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8285
              else ());
             (let c1 =
                let uu____8288 = FStar_TypeChecker_Env.should_verify env in
                if uu____8288
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
              (let uu____8291 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8291
               then
                 let uu____8292 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8292
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8353 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8353 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8483 =
             match uu____8483 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8549 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8549
                   then
                     let uu____8550 =
                       let uu____8551 =
                         let uu____8554 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8554
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8551
                         (FStar_String.concat ", ") in
                     let uu____8581 =
                       let uu____8582 =
                         let uu____8585 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8585
                           (FStar_List.map
                              (fun uu____8613  ->
                                 match uu____8613 with
                                 | (u,t2) ->
                                     let uu____8620 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8621 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8620 uu____8621)) in
                       FStar_All.pipe_right uu____8582
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8550
                       uu____8581
                   else ());
                  (let univs2 =
                     let uu____8628 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8651  ->
                            match uu____8651 with
                            | (uu____8660,t2) ->
                                let uu____8662 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8662)
                       univs1 uu____8628 in
                   let uvs = gen_uvars uvt in
                   (let uu____8685 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8685
                    then
                      let uu____8686 =
                        let uu____8687 =
                          let uu____8690 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8690
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8687
                          (FStar_String.concat ", ") in
                      let uu____8717 =
                        let uu____8718 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8750  ->
                                  match uu____8750 with
                                  | (u,t2) ->
                                      let uu____8757 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8758 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8757 uu____8758)) in
                        FStar_All.pipe_right uu____8718
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8686
                        uu____8717
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8788 =
             let uu____8821 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8821 in
           match uu____8788 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8939 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8939
                 then ()
                 else
                   (let uu____8941 = lec_hd in
                    match uu____8941 with
                    | (lb1,uu____8949,uu____8950) ->
                        let uu____8951 = lec2 in
                        (match uu____8951 with
                         | (lb2,uu____8959,uu____8960) ->
                             let msg =
                               let uu____8962 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8963 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8962 uu____8963 in
                             let uu____8964 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8964)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9075  ->
                           match uu____9075 with
                           | (u,uu____9083) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9105  ->
                                       match uu____9105 with
                                       | (u',uu____9113) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9118 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9118
                 then ()
                 else
                   (let uu____9120 = lec_hd in
                    match uu____9120 with
                    | (lb1,uu____9128,uu____9129) ->
                        let uu____9130 = lec2 in
                        (match uu____9130 with
                         | (lb2,uu____9138,uu____9139) ->
                             let msg =
                               let uu____9141 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9142 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9141 uu____9142 in
                             let uu____9143 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9143)) in
               let lecs1 =
                 let uu____9153 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9212 = univs_and_uvars_of_lec this_lec in
                        match uu____9212 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9153 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9365 = lec_hd in
                   match uu____9365 with
                   | (lbname,e,c) ->
                       let uu____9375 =
                         let uu____9380 =
                           let uu____9381 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____9382 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____9383 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9381 uu____9382 uu____9383 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9380) in
                       let uu____9384 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____9375 uu____9384 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9414  ->
                         match uu____9414 with
                         | (u,k) ->
                             let uu____9427 = FStar_Syntax_Unionfind.find u in
                             (match uu____9427 with
                              | FStar_Pervasives_Native.Some uu____9436 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9443 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9447 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9447 with
                                   | (bs,kres) ->
                                       ((let uu____9485 =
                                           let uu____9486 =
                                             let uu____9489 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9489 in
                                           uu____9486.FStar_Syntax_Syntax.n in
                                         match uu____9485 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9490 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9494 =
                                               let uu____9495 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9495 in
                                             if uu____9494
                                             then fail kres
                                             else ()
                                         | uu____9497 -> fail kres);
                                        (let a =
                                           let uu____9499 =
                                             let uu____9502 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9502 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9499 kres in
                                         let t =
                                           let uu____9506 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9506
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
                      (fun uu____9625  ->
                         match uu____9625 with
                         | (lbname,e,c) ->
                             let uu____9671 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9740 ->
                                   let uu____9755 = (e, c) in
                                   (match uu____9755 with
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
                                                (fun uu____9792  ->
                                                   match uu____9792 with
                                                   | (x,uu____9800) ->
                                                       let uu____9805 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9805)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9815 =
                                                let uu____9816 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9816 in
                                              if uu____9815
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
                                          let uu____9824 =
                                            let uu____9825 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9825.FStar_Syntax_Syntax.n in
                                          match uu____9824 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9848 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9848 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9863 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9865 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9865, gen_tvars)) in
                             (match uu____9671 with
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
        (let uu____10011 = Obj.magic () in ());
        (let uu____10013 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____10013
         then
           let uu____10014 =
             let uu____10015 =
               FStar_List.map
                 (fun uu____10028  ->
                    match uu____10028 with
                    | (lb,uu____10036,uu____10037) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____10015 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____10014
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10058  ->
                match uu____10058 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10087 = gen env is_rec lecs in
           match uu____10087 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10186  ->
                       match uu____10186 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10248 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10248
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10292  ->
                           match uu____10292 with
                           | (l,us,e,c,gvs) ->
                               let uu____10326 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10327 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10328 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10329 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10330 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10326 uu____10327 uu____10328
                                 uu____10329 uu____10330))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10371  ->
                match uu____10371 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10415 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10415, t, c, gvs)) univnames_lecs
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
              (let uu____10458 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10458 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10464 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10464) in
          let is_var e1 =
            let uu____10471 =
              let uu____10472 = FStar_Syntax_Subst.compress e1 in
              uu____10472.FStar_Syntax_Syntax.n in
            match uu____10471 with
            | FStar_Syntax_Syntax.Tm_name uu____10475 -> true
            | uu____10476 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___127_10492 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___127_10492.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___127_10492.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10493 -> e2 in
          let env2 =
            let uu___128_10495 = env1 in
            let uu____10496 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___128_10495.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___128_10495.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___128_10495.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___128_10495.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___128_10495.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___128_10495.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___128_10495.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___128_10495.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___128_10495.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___128_10495.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___128_10495.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___128_10495.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___128_10495.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___128_10495.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___128_10495.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10496;
              FStar_TypeChecker_Env.is_iface =
                (uu___128_10495.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___128_10495.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___128_10495.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___128_10495.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___128_10495.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___128_10495.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___128_10495.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___128_10495.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___128_10495.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___128_10495.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___128_10495.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___128_10495.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___128_10495.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___128_10495.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___128_10495.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___128_10495.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___128_10495.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___128_10495.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10497 = check env2 t1 t2 in
          match uu____10497 with
          | FStar_Pervasives_Native.None  ->
              let uu____10504 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____10509 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____10504 uu____10509
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10516 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10516
                then
                  let uu____10517 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10517
                else ());
               (let uu____10519 = decorate e t2 in (uu____10519, g)))
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
        let uu____10547 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10547
        then
          let uu____10552 = discharge g1 in
          let uu____10553 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10552, uu____10553)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10566 =
               let uu____10567 =
                 let uu____10568 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10568 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10567
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10566
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10570 = destruct_comp c1 in
           match uu____10570 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10587 = FStar_TypeChecker_Env.get_range env in
                 let uu____10588 =
                   let uu____10589 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10590 =
                     let uu____10591 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10592 =
                       let uu____10595 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10595] in
                     uu____10591 :: uu____10592 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10589 uu____10590 in
                 uu____10588 FStar_Pervasives_Native.None uu____10587 in
               ((let uu____10599 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10599
                 then
                   let uu____10600 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10600
                 else ());
                (let g2 =
                   let uu____10603 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10603 in
                 let uu____10604 = discharge g2 in
                 let uu____10605 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10604, uu____10605))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___87_10629 =
        match uu___87_10629 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10637)::[] -> f fst1
        | uu____10654 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10659 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10659
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10668 =
          let uu____10671 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10671 in
        FStar_All.pipe_right uu____10668
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10682 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10682
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___88_10696 =
        match uu___88_10696 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10704)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10723)::[] ->
            let uu____10752 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10752
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10757 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10767 =
          let uu____10774 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10774) in
        let uu____10779 =
          let uu____10788 =
            let uu____10795 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10795) in
          let uu____10800 =
            let uu____10809 =
              let uu____10816 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10816) in
            let uu____10821 =
              let uu____10830 =
                let uu____10837 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10837) in
              let uu____10842 =
                let uu____10851 =
                  let uu____10858 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10858) in
                [uu____10851; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10830 :: uu____10842 in
            uu____10809 :: uu____10821 in
          uu____10788 :: uu____10800 in
        uu____10767 :: uu____10779 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10909 =
            FStar_Util.find_map table
              (fun uu____10922  ->
                 match uu____10922 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10939 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10939
                     else FStar_Pervasives_Native.None) in
          (match uu____10909 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10942 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10946 =
      let uu____10947 = FStar_Syntax_Util.un_uinst l in
      uu____10947.FStar_Syntax_Syntax.n in
    match uu____10946 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10951 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10975)::uu____10976 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10987 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10994,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10995))::uu____10996 -> bs
      | uu____11013 ->
          let uu____11014 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11014 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11018 =
                 let uu____11019 = FStar_Syntax_Subst.compress t in
                 uu____11019.FStar_Syntax_Syntax.n in
               (match uu____11018 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11023) ->
                    let uu____11040 =
                      FStar_Util.prefix_until
                        (fun uu___89_11080  ->
                           match uu___89_11080 with
                           | (uu____11087,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11088)) ->
                               false
                           | uu____11091 -> true) bs' in
                    (match uu____11040 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11126,uu____11127) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11199,uu____11200) ->
                         let uu____11273 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11291  ->
                                   match uu____11291 with
                                   | (x,uu____11299) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11273
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11346  ->
                                     match uu____11346 with
                                     | (x,i) ->
                                         let uu____11365 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11365, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11375 -> bs))
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
          let uu____11407 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11407
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
        (let uu____11430 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11430
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11432 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11432))
         else ());
        (let fv =
           let uu____11435 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11435
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
         let uu____11443 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___129_11449 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___129_11449.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___129_11449.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___129_11449.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___129_11449.FStar_Syntax_Syntax.sigattrs)
           }), uu____11443))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___90_11459 =
        match uu___90_11459 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11460 -> false in
      let reducibility uu___91_11464 =
        match uu___91_11464 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11465 -> false in
      let assumption uu___92_11469 =
        match uu___92_11469 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11470 -> false in
      let reification uu___93_11474 =
        match uu___93_11474 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11475 -> true
        | uu____11476 -> false in
      let inferred uu___94_11480 =
        match uu___94_11480 with
        | FStar_Syntax_Syntax.Discriminator uu____11481 -> true
        | FStar_Syntax_Syntax.Projector uu____11482 -> true
        | FStar_Syntax_Syntax.RecordType uu____11487 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11496 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11505 -> false in
      let has_eq uu___95_11509 =
        match uu___95_11509 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11510 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11570 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11575 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11579 =
        let uu____11580 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___96_11584  ->
                  match uu___96_11584 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11585 -> false)) in
        FStar_All.pipe_right uu____11580 Prims.op_Negation in
      if uu____11579
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11598 =
            let uu____11603 =
              let uu____11604 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11604 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11603) in
          FStar_Errors.raise_error uu____11598 r in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11612 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11616 =
            let uu____11617 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11617 in
          if uu____11616 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11622),uu____11623) ->
              ((let uu____11639 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11639
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11643 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11643
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11649 ->
              let uu____11658 =
                let uu____11659 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11659 in
              if uu____11658 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11665 ->
              let uu____11672 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11672 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11676 ->
              let uu____11683 =
                let uu____11684 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11684 in
              if uu____11683 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11690 ->
              let uu____11691 =
                let uu____11692 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11692 in
              if uu____11691 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11698 ->
              let uu____11699 =
                let uu____11700 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11700 in
              if uu____11699 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11706 ->
              let uu____11719 =
                let uu____11720 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11720 in
              if uu____11719 then err'1 () else ()
          | uu____11726 -> ()))
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
                          let uu____11789 =
                            let uu____11792 =
                              let uu____11793 =
                                let uu____11800 =
                                  let uu____11801 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11801 in
                                (uu____11800, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11793 in
                            FStar_Syntax_Syntax.mk uu____11792 in
                          uu____11789 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11842  ->
                                  match uu____11842 with
                                  | (x,imp) ->
                                      let uu____11853 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11853, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11855 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11855 in
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
                             let uu____11864 =
                               let uu____11865 =
                                 let uu____11866 =
                                   let uu____11867 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11868 =
                                     let uu____11869 =
                                       let uu____11870 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11870 in
                                     [uu____11869] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11867
                                     uu____11868 in
                                 uu____11866 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11865 in
                             FStar_Syntax_Util.refine x uu____11864 in
                           let uu____11873 =
                             let uu___130_11874 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___130_11874.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___130_11874.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11873) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11889 =
                          FStar_List.map
                            (fun uu____11911  ->
                               match uu____11911 with
                               | (x,uu____11923) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11889 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11972  ->
                                match uu____11972 with
                                | (x,uu____11984) ->
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
                             (let uu____11998 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11998)
                               ||
                               (let uu____12000 =
                                  let uu____12001 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12001.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12000) in
                           let quals =
                             let uu____12005 =
                               let uu____12008 =
                                 let uu____12011 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12011
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12015 =
                                 FStar_List.filter
                                   (fun uu___97_12019  ->
                                      match uu___97_12019 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12020 -> false) iquals in
                               FStar_List.append uu____12008 uu____12015 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12005 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12041 =
                                 let uu____12042 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12042 in
                               FStar_Syntax_Syntax.mk_Total uu____12041 in
                             let uu____12043 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12043 in
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
                           (let uu____12046 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12046
                            then
                              let uu____12047 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12047
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
                                             fun uu____12100  ->
                                               match uu____12100 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12124 =
                                                       let uu____12127 =
                                                         let uu____12128 =
                                                           let uu____12135 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12135,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12128 in
                                                       pos uu____12127 in
                                                     (uu____12124, b)
                                                   else
                                                     (let uu____12139 =
                                                        let uu____12142 =
                                                          let uu____12143 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12143 in
                                                        pos uu____12142 in
                                                      (uu____12139, b)))) in
                                   let pat_true =
                                     let uu____12161 =
                                       let uu____12164 =
                                         let uu____12165 =
                                           let uu____12178 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12178, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12165 in
                                       pos uu____12164 in
                                     (uu____12161,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12212 =
                                       let uu____12215 =
                                         let uu____12216 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12216 in
                                       pos uu____12215 in
                                     (uu____12212,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12228 =
                                     let uu____12231 =
                                       let uu____12232 =
                                         let uu____12255 =
                                           let uu____12258 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12259 =
                                             let uu____12262 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12262] in
                                           uu____12258 :: uu____12259 in
                                         (arg_exp, uu____12255) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12232 in
                                     FStar_Syntax_Syntax.mk uu____12231 in
                                   uu____12228 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12269 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12269
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
                                let uu____12277 =
                                  let uu____12282 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12282 in
                                let uu____12283 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12277;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12283
                                } in
                              let impl =
                                let uu____12287 =
                                  let uu____12288 =
                                    let uu____12295 =
                                      let uu____12298 =
                                        let uu____12299 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12299
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12298] in
                                    ((false, [lb]), uu____12295) in
                                  FStar_Syntax_Syntax.Sig_let uu____12288 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12287;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12317 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12317
                               then
                                 let uu____12318 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12318
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
                                fun uu____12360  ->
                                  match uu____12360 with
                                  | (a,uu____12366) ->
                                      let uu____12367 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12367 with
                                       | (field_name,uu____12373) ->
                                           let field_proj_tm =
                                             let uu____12375 =
                                               let uu____12376 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12376 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12375 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12393 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12425  ->
                                    match uu____12425 with
                                    | (x,uu____12433) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12435 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12435 with
                                         | (field_name,uu____12443) ->
                                             let t =
                                               let uu____12445 =
                                                 let uu____12446 =
                                                   let uu____12449 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12449 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12446 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12445 in
                                             let only_decl =
                                               (let uu____12453 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12453)
                                                 ||
                                                 (let uu____12455 =
                                                    let uu____12456 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12456.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12455) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12470 =
                                                   FStar_List.filter
                                                     (fun uu___98_12474  ->
                                                        match uu___98_12474
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12475 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12470
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___99_12488  ->
                                                         match uu___99_12488
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12489 ->
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
                                             ((let uu____12508 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12508
                                               then
                                                 let uu____12509 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12509
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
                                                           fun uu____12557 
                                                             ->
                                                             match uu____12557
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12581
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12581,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12597
                                                                    =
                                                                    let uu____12600
                                                                    =
                                                                    let uu____12601
                                                                    =
                                                                    let uu____12608
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12608,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12601 in
                                                                    pos
                                                                    uu____12600 in
                                                                    (uu____12597,
                                                                    b))
                                                                   else
                                                                    (let uu____12612
                                                                    =
                                                                    let uu____12615
                                                                    =
                                                                    let uu____12616
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12616 in
                                                                    pos
                                                                    uu____12615 in
                                                                    (uu____12612,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12632 =
                                                     let uu____12635 =
                                                       let uu____12636 =
                                                         let uu____12649 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12649,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12636 in
                                                     pos uu____12635 in
                                                   let uu____12658 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12632,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12658) in
                                                 let body =
                                                   let uu____12670 =
                                                     let uu____12673 =
                                                       let uu____12674 =
                                                         let uu____12697 =
                                                           let uu____12700 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12700] in
                                                         (arg_exp,
                                                           uu____12697) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12674 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12673 in
                                                   uu____12670
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12708 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12708
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
                                                   let uu____12715 =
                                                     let uu____12720 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12720 in
                                                   let uu____12721 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12715;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12721
                                                   } in
                                                 let impl =
                                                   let uu____12725 =
                                                     let uu____12726 =
                                                       let uu____12733 =
                                                         let uu____12736 =
                                                           let uu____12737 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12737
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12736] in
                                                       ((false, [lb]),
                                                         uu____12733) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12726 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12725;
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
                                                 (let uu____12755 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12755
                                                  then
                                                    let uu____12756 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12756
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12393 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12796) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12801 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12801 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12823 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12823 with
                    | (formals,uu____12839) ->
                        let uu____12856 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12888 =
                                   let uu____12889 =
                                     let uu____12890 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12890 in
                                   FStar_Ident.lid_equals typ_lid uu____12889 in
                                 if uu____12888
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12909,uvs',tps,typ0,uu____12913,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12932 -> failwith "Impossible"
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
                        (match uu____12856 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13005 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13005 with
                              | (indices,uu____13021) ->
                                  let refine_domain =
                                    let uu____13039 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___100_13044  ->
                                              match uu___100_13044 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13045 -> true
                                              | uu____13054 -> false)) in
                                    if uu____13039
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___101_13062 =
                                      match uu___101_13062 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13065,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13077 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13078 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13078 with
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
                                    let uu____13089 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13089 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13154  ->
                                               fun uu____13155  ->
                                                 match (uu____13154,
                                                         uu____13155)
                                                 with
                                                 | ((x,uu____13173),(x',uu____13175))
                                                     ->
                                                     let uu____13184 =
                                                       let uu____13191 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13191) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13184) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13192 -> []