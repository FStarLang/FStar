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
  fun uu___79_93  ->
    match uu___79_93 with
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
                     let uu___103_257 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u in
                         (reason, env, uu____286, t, k, r) in
                       [uu____273] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___103_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___103_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___103_257.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___104_497 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_497.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_497.FStar_Syntax_Syntax.index);
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
                ((let uu___105_1126 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___105_1126.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___105_1126.FStar_Syntax_Syntax.index);
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
                       let uu___106_1237 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_1237.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_1237.FStar_Syntax_Syntax.index);
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
                            let uu___107_1269 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___107_1269.FStar_Syntax_Syntax.p)
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
                       (let uu___108_1991 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___108_1991.FStar_Syntax_Syntax.p)
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
                          let uu___109_2574 = p1 in
                          let uu____2577 =
                            let uu____2578 =
                              let uu____2591 = aux f pats1 in
                              (fv, uu____2591) in
                            FStar_Syntax_Syntax.Pat_cons uu____2578 in
                          {
                            FStar_Syntax_Syntax.v = uu____2577;
                            FStar_Syntax_Syntax.p =
                              (uu___109_2574.FStar_Syntax_Syntax.p)
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
                  let uu___110_2860 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___110_2860.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___110_2860.FStar_Syntax_Syntax.index);
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
                  let uu___111_2871 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___111_2871.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___111_2871.FStar_Syntax_Syntax.index);
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
      let uu____4321 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4321
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4324  ->
           let uu____4325 = FStar_Syntax_Syntax.lcomp_comp lc in
           FStar_Syntax_Subst.subst_comp subst1 uu____4325)
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4329 =
      let uu____4330 = FStar_Syntax_Subst.compress t in
      uu____4330.FStar_Syntax_Syntax.n in
    match uu____4329 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4333 -> true
    | uu____4346 -> false
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
              let uu____4384 =
                let uu____4385 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4385 in
              if uu____4384
              then f
              else (let uu____4387 = reason1 () in label uu____4387 r f)
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
            let uu___112_4398 = g in
            let uu____4399 =
              let uu____4400 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4400 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4399;
              FStar_TypeChecker_Env.deferred =
                (uu___112_4398.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___112_4398.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___112_4398.FStar_TypeChecker_Env.implicits)
            }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4414 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4414
        then c
        else
          (let uu____4416 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4416
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4455 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4455] in
                       let us =
                         let uu____4459 =
                           let uu____4462 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4462] in
                         u_res :: uu____4459 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4466 =
                         let uu____4467 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4468 =
                           let uu____4469 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4470 =
                             let uu____4473 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4474 =
                               let uu____4477 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4477] in
                             uu____4473 :: uu____4474 in
                           uu____4469 :: uu____4470 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4467 uu____4468 in
                       uu____4466 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4481 = destruct_comp c1 in
              match uu____4481 with
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
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____4508  ->
             let uu____4509 = FStar_Syntax_Syntax.lcomp_comp lc in
             close_comp env bvs uu____4509)
let should_not_inline_lc: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___80_4516  ->
            match uu___80_4516 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4517 -> false))
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
                (let uu____4533 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
                 Prims.op_Negation uu____4533))
               &&
               (let uu____4540 = FStar_Syntax_Util.head_and_args' e in
                match uu____4540 with
                | (head1,uu____4554) ->
                    let uu____4571 =
                      let uu____4572 = FStar_Syntax_Util.un_uinst head1 in
                      uu____4572.FStar_Syntax_Syntax.n in
                    (match uu____4571 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4576 =
                           let uu____4577 = FStar_Syntax_Syntax.lid_of_fv fv in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4577 in
                         Prims.op_Negation uu____4576
                     | uu____4578 -> true)))
              &&
              (let uu____4580 = should_not_inline_lc lc in
               Prims.op_Negation uu____4580)
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
            let uu____4598 =
              let uu____4599 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid in
              FStar_All.pipe_left Prims.op_Negation uu____4599 in
            if uu____4598
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4601 = FStar_Syntax_Util.is_unit t in
               if uu____4601
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
                    let uu____4607 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4607
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4609 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid in
                       match uu____4609 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp in
                           let uu____4617 =
                             let uu____4618 =
                               let uu____4619 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                               let uu____4620 =
                                 let uu____4621 =
                                   FStar_Syntax_Syntax.as_arg t in
                                 let uu____4622 =
                                   let uu____4625 =
                                     FStar_Syntax_Syntax.as_arg v1 in
                                   [uu____4625] in
                                 uu____4621 :: uu____4622 in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4619
                                 uu____4620 in
                             uu____4618 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4617) in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
          (let uu____4629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return") in
           if uu____4629
           then
             let uu____4630 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
             let uu____4631 = FStar_Syntax_Print.term_to_string v1 in
             let uu____4632 =
               FStar_TypeChecker_Normalize.comp_to_string env c in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4630 uu____4631 uu____4632
           else ());
          c
let weaken_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    let uu____4643 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___81_4647  ->
              match uu___81_4647 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4648 -> false)) in
    if uu____4643
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___82_4657  ->
              match uu___82_4657 with
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
        let uu____4670 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4670
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
           let uu____4673 = destruct_comp c1 in
           match uu____4673 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name in
               let wp1 =
                 let uu____4687 =
                   let uu____4688 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p in
                   let uu____4689 =
                     let uu____4690 = FStar_Syntax_Syntax.as_arg res_t in
                     let uu____4691 =
                       let uu____4694 = FStar_Syntax_Syntax.as_arg formula in
                       let uu____4695 =
                         let uu____4698 = FStar_Syntax_Syntax.as_arg wp in
                         [uu____4698] in
                       uu____4694 :: uu____4695 in
                     uu____4690 :: uu____4691 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4688 uu____4689 in
                 uu____4687 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos in
               let uu____4701 = weaken_flags c1.FStar_Syntax_Syntax.flags in
               mk_comp md u_res_t res_t wp1 uu____4701)
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4716 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc in
          let uu____4718 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____4718
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1) in
        let uu____4721 = weaken_flags lc.FStar_Syntax_Syntax.cflags in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4721 weaken
let strengthen_comp:
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
               let uu____4754 = destruct_comp c1 in
               match uu____4754 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name in
                   let wp1 =
                     let uu____4768 =
                       let uu____4769 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p in
                       let uu____4770 =
                         let uu____4771 = FStar_Syntax_Syntax.as_arg res_t in
                         let uu____4772 =
                           let uu____4775 =
                             let uu____4776 =
                               let uu____4777 =
                                 FStar_TypeChecker_Env.get_range env in
                               label_opt env reason uu____4777 f in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____4776 in
                           let uu____4778 =
                             let uu____4781 = FStar_Syntax_Syntax.as_arg wp in
                             [uu____4781] in
                           uu____4775 :: uu____4778 in
                         uu____4771 :: uu____4772 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4769 uu____4770 in
                     uu____4768 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos in
                   mk_comp md u_res_t res_t wp1 flags1)
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
            let uu____4816 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____4816
            then (lc, g0)
            else
              (let flags1 =
                 let uu____4825 =
                   let uu____4832 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc in
                   if uu____4832
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, []) in
                 match uu____4825 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____4852 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___83_4860  ->
                               match uu___83_4860 with
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
                               | uu____4863 -> [])) in
                     FStar_List.append flags1 uu____4852 in
               let strengthen uu____4867 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                    let uu____4871 = FStar_TypeChecker_Rel.guard_form g01 in
                    match uu____4871 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____4874 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme in
                          if uu____4874
                          then
                            let uu____4875 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only in
                            let uu____4876 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____4875 uu____4876
                          else ());
                         strengthen_comp env reason c f flags1)) in
               let uu____4878 =
                 let uu____4879 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name in
                 FStar_Syntax_Syntax.mk_lcomp uu____4879
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen in
               (uu____4878,
                 (let uu___113_4881 = g0 in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___113_4881.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___113_4881.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___113_4881.FStar_TypeChecker_Env.implicits)
                  })))
let lcomp_has_trivial_postcondition: FStar_Syntax_Syntax.lcomp -> Prims.bool
  =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___84_4886  ->
            match uu___84_4886 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4887 -> false) lc.FStar_Syntax_Syntax.cflags)
let maybe_add_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____4904 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax in
          if uu____4904
          then e
          else
            (let uu____4906 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4908 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid in
                  FStar_Option.isSome uu____4908) in
             if uu____4906
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
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
          fun uu____4946  ->
            match uu____4946 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4964 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4964 then f () else () in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                let bind_flags =
                  let uu____4972 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21) in
                  if uu____4972
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4979 = FStar_Syntax_Util.is_total_lcomp lc11 in
                       if uu____4979
                       then
                         let uu____4982 =
                           FStar_Syntax_Util.is_total_lcomp lc21 in
                         (if uu____4982
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4986 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21 in
                             if uu____4986
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4991 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21) in
                          if uu____4991
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else []) in
                     let uu____4995 = lcomp_has_trivial_postcondition lc21 in
                     if uu____4995
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1) in
                let bind_it uu____5002 =
                  let uu____5003 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____5003
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11 in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21 in
                     debug1
                       (fun uu____5017  ->
                          let uu____5018 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____5019 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____5021 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5018 uu____5019 uu____5021);
                     (let aux uu____5033 =
                        let uu____5034 = FStar_Syntax_Util.is_trivial_wp c1 in
                        if uu____5034
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5055 ->
                              let uu____5056 =
                                FStar_Syntax_Util.is_ml_comp c2 in
                              (if uu____5056
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5075 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2) in
                           if uu____5075
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML") in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5142 =
                              let uu____5147 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2 in
                              (uu____5147, reason) in
                            FStar_Util.Inl uu____5142
                        | uu____5154 -> aux () in
                      let try_simplify uu____5176 =
                        let rec maybe_close t x c =
                          let uu____5187 =
                            let uu____5188 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t in
                            uu____5188.FStar_Syntax_Syntax.n in
                          match uu____5187 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5192) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5198 -> c in
                        let uu____5199 =
                          let uu____5200 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid in
                          FStar_Option.isNone uu____5200 in
                        if uu____5199
                        then
                          let uu____5211 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                          (if uu____5211
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5225 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5225))
                        else
                          (let uu____5235 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2) in
                           if uu____5235
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5245 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                              if uu____5245
                              then
                                let uu____5254 =
                                  let uu____5259 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2) in
                                  (uu____5259, "both gtot") in
                                FStar_Util.Inl uu____5254
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5283 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5285 =
                                            FStar_Syntax_Syntax.is_null_bv x in
                                          Prims.op_Negation uu____5285) in
                                     if uu____5283
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                       let x1 =
                                         let uu___114_5296 = x in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___114_5296.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___114_5296.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         } in
                                       let uu____5297 =
                                         let uu____5302 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21 in
                                         (uu____5302, "c1 Tot") in
                                       FStar_Util.Inl uu____5297
                                     else aux ()
                                 | uu____5308 -> aux ()))) in
                      let uu____5317 = try_simplify () in
                      match uu____5317 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5337  ->
                                let uu____5338 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5338);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5347  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5362 = lift_and_destruct env c11 c21 in
                              match uu____5362 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5419 =
                                          FStar_Syntax_Syntax.null_binder t1 in
                                        [uu____5419]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5421 =
                                          FStar_Syntax_Syntax.mk_binder x in
                                        [uu____5421] in
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
                                    let uu____5434 =
                                      FStar_Syntax_Syntax.as_arg r11 in
                                    let uu____5435 =
                                      let uu____5438 =
                                        FStar_Syntax_Syntax.as_arg t1 in
                                      let uu____5439 =
                                        let uu____5442 =
                                          FStar_Syntax_Syntax.as_arg t2 in
                                        let uu____5443 =
                                          let uu____5446 =
                                            FStar_Syntax_Syntax.as_arg wp1 in
                                          let uu____5447 =
                                            let uu____5450 =
                                              let uu____5451 = mk_lam wp2 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5451 in
                                            [uu____5450] in
                                          uu____5446 :: uu____5447 in
                                        uu____5442 :: uu____5443 in
                                      uu____5438 :: uu____5439 in
                                    uu____5434 :: uu____5435 in
                                  let wp =
                                    let uu____5455 =
                                      let uu____5456 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5456 wp_args in
                                    uu____5455 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos in
                                  mk_comp md u_t2 t2 wp bind_flags in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21 in
                              let uu____5475 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name in
                              match uu____5475 with
                              | (m,uu____5483,lift2) ->
                                  let c23 =
                                    let uu____5486 = lift_comp c22 m lift2 in
                                    FStar_Syntax_Syntax.mk_Comp uu____5486 in
                                  let uu____5487 = destruct_comp c12 in
                                  (match uu____5487 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name in
                                       let vc1 =
                                         let uu____5501 =
                                           let uu____5502 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial in
                                           let uu____5503 =
                                             let uu____5504 =
                                               FStar_Syntax_Syntax.as_arg t1 in
                                             let uu____5505 =
                                               let uu____5508 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1 in
                                               [uu____5508] in
                                             uu____5504 :: uu____5505 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5502 uu____5503 in
                                         uu____5501
                                           FStar_Pervasives_Native.None r1 in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags) in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____5514 = destruct_comp c1_typ in
                            match uu____5514 with
                            | (u_res_t1,res_t1,uu____5523) ->
                                let uu____5524 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11) in
                                if uu____5524
                                then
                                  let e1 = FStar_Option.get e1opt in
                                  let x = FStar_Option.get b in
                                  let uu____5527 =
                                    FStar_Syntax_Util.is_partial_return c1 in
                                  (if uu____5527
                                   then
                                     (debug1
                                        (fun uu____5535  ->
                                           let uu____5536 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1 in
                                           let uu____5537 =
                                             FStar_Syntax_Print.bv_to_string
                                               x in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5536 uu____5537);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2 in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5540 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5542 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid in
                                           FStar_Option.isSome uu____5542) in
                                      if uu____5540
                                      then
                                        let e1' =
                                          let uu____5564 =
                                            FStar_Options.vcgen_decorate_with_type
                                              () in
                                          if uu____5564
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1 in
                                        (debug1
                                           (fun uu____5575  ->
                                              let uu____5576 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1' in
                                              let uu____5577 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5576 uu____5577);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2 in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5589  ->
                                              let uu____5590 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1 in
                                              let uu____5591 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5590 uu____5591);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2 in
                                          let x_eq_e =
                                            let uu____5594 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5594 in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2)))) in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
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
      | uu____5606 -> g2
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
            (let uu____5622 = FStar_Syntax_Util.is_lcomp_partial_return lc in
             Prims.op_Negation uu____5622) in
        let flags1 =
          if should_return1
          then
            let uu____5628 = FStar_Syntax_Util.is_total_lcomp lc in
            (if uu____5628
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5636 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c) in
          let uu____5640 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
          if uu____5640
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e in
            let uu____5642 =
              let uu____5643 = FStar_Syntax_Util.is_pure_comp c in
              Prims.op_Negation uu____5643 in
            (if uu____5642
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
               let retc2 =
                 let uu___115_5646 = retc1 in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___115_5646.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___115_5646.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___115_5646.FStar_Syntax_Syntax.effect_args);
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
               let uu____5657 =
                 let uu____5660 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp in
                 FStar_Syntax_Util.comp_set_flags uu____5660
                   [FStar_Syntax_Syntax.PARTIAL_RETURN] in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5657 in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1) in
             let uu____5665 =
               let uu____5666 =
                 let uu____5667 = FStar_Syntax_Util.lcomp_of_comp c2 in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5667
                   ((FStar_Pervasives_Native.Some x), eq_ret) in
               FStar_Syntax_Syntax.lcomp_comp uu____5666 in
             FStar_Syntax_Util.comp_set_flags uu____5665 flags1) in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
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
            fun uu____5690  ->
              match uu____5690 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name in
                    let uu____5702 =
                      ((let uu____5705 = is_pure_or_ghost_effect env eff1 in
                        Prims.op_Negation uu____5705) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2) in
                    if uu____5702
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2 in
                  bind r env e1opt lc1 (x, lc21)
let fvar_const:
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____5715 =
        let uu____5716 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5716 in
      FStar_Syntax_Syntax.fvar uu____5715 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5775  ->
                 match uu____5775 with
                 | (uu____5788,eff_label,uu____5790,uu____5791) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let uu____5800 =
          let uu____5807 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5839  ->
                    match uu____5839 with
                    | (uu____5852,uu____5853,flags1,uu____5855) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___85_5867  ->
                                match uu___85_5867 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5868 -> false)))) in
          if uu____5807
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, []) in
        match uu____5800 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5889 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
              let uu____5891 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
              if uu____5891
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5911 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos in
                   let uu____5912 =
                     let uu____5913 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else in
                     let uu____5914 =
                       let uu____5915 = FStar_Syntax_Syntax.as_arg res_t1 in
                       let uu____5916 =
                         let uu____5919 = FStar_Syntax_Syntax.as_arg g in
                         let uu____5920 =
                           let uu____5923 = FStar_Syntax_Syntax.as_arg wp_t in
                           let uu____5924 =
                             let uu____5927 = FStar_Syntax_Syntax.as_arg wp_e in
                             [uu____5927] in
                           uu____5923 :: uu____5924 in
                         uu____5919 :: uu____5920 in
                       uu____5915 :: uu____5916 in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5913 uu____5914 in
                   uu____5912 FStar_Pervasives_Native.None uu____5911 in
                 let default_case =
                   let post_k =
                     let uu____5934 =
                       let uu____5941 = FStar_Syntax_Syntax.null_binder res_t in
                       [uu____5941] in
                     let uu____5942 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5934 uu____5942 in
                   let kwp =
                     let uu____5948 =
                       let uu____5955 =
                         FStar_Syntax_Syntax.null_binder post_k in
                       [uu____5955] in
                     let uu____5956 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                     FStar_Syntax_Util.arrow uu____5948 uu____5956 in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k in
                   let wp =
                     let uu____5961 =
                       let uu____5962 = FStar_Syntax_Syntax.mk_binder post in
                       [uu____5962] in
                     let uu____5963 =
                       let uu____5964 =
                         let uu____5967 = FStar_TypeChecker_Env.get_range env in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____5967 in
                       let uu____5968 =
                         fvar_const env FStar_Parser_Const.false_lid in
                       FStar_All.pipe_left uu____5964 uu____5968 in
                     FStar_Syntax_Util.abs uu____5961 uu____5963
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
                   let uu____5984 =
                     should_not_inline_whole_match ||
                       (let uu____5986 = is_pure_or_ghost_effect env eff in
                        Prims.op_Negation uu____5986) in
                   if uu____5984 then cthen true else cthen false in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6018  ->
                        fun celse  ->
                          match uu____6018 with
                          | (g,eff_label,uu____6034,cthen) ->
                              let uu____6044 =
                                let uu____6069 =
                                  let uu____6070 =
                                    maybe_return eff_label cthen in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6070 in
                                lift_and_destruct env uu____6069 celse in
                              (match uu____6044 with
                               | ((md,uu____6072,uu____6073),(uu____6074,uu____6075,wp_then),
                                  (uu____6077,uu____6078,wp_else)) ->
                                   let uu____6098 =
                                     ifthenelse md res_t g wp_then wp_else in
                                   mk_comp md u_res_t res_t uu____6098 []))
                     lcases default_case in
                 match lcases with
                 | [] -> comp
                 | uu____6111::[] -> comp
                 | uu____6148 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name in
                     let uu____6165 = destruct_comp comp1 in
                     (match uu____6165 with
                      | (uu____6172,uu____6173,wp) ->
                          let wp1 =
                            let uu____6178 =
                              let uu____6179 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp in
                              let uu____6180 =
                                let uu____6181 =
                                  FStar_Syntax_Syntax.as_arg res_t in
                                let uu____6182 =
                                  let uu____6185 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____6185] in
                                uu____6181 :: uu____6182 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6179
                                uu____6180 in
                            uu____6178 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags)) in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
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
          let uu____6212 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6212 with
          | FStar_Pervasives_Native.None  ->
              let uu____6221 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c' in
              let uu____6226 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____6221 uu____6226
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
            let uu____6259 =
              let uu____6260 = FStar_Syntax_Subst.compress t2 in
              uu____6260.FStar_Syntax_Syntax.n in
            match uu____6259 with
            | FStar_Syntax_Syntax.Tm_type uu____6263 -> true
            | uu____6264 -> false in
          let uu____6265 =
            let uu____6266 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6266.FStar_Syntax_Syntax.n in
          match uu____6265 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6274 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6285 =
                  let uu____6286 =
                    let uu____6287 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6287 in
                  (FStar_Pervasives_Native.None, uu____6286) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6285 in
              let e1 =
                let uu____6297 =
                  let uu____6298 =
                    let uu____6299 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6299] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6298 in
                uu____6297 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6304 -> (e, lc)
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
              (let uu____6333 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6333 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6356 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6378 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6378, false)
            else
              (let uu____6384 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6384, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6395) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6404 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ in
                FStar_Errors.raise_error uu____6404 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___116_6418 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___116_6418.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___116_6418.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___116_6418.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6423 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6423 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___117_6431 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___117_6431.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___117_6431.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___117_6431.FStar_Syntax_Syntax.comp_thunk)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___118_6434 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___118_6434.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___118_6434.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___118_6434.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6438 =
                     let uu____6439 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6439
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6442 =
                          let uu____6443 = FStar_Syntax_Subst.compress f1 in
                          uu____6443.FStar_Syntax_Syntax.n in
                        match uu____6442 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6446,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6448;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6449;_},uu____6450)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___119_6472 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___119_6472.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___119_6472.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___119_6472.FStar_Syntax_Syntax.comp_thunk)
                              } in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6473 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc in
                            ((let uu____6476 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6476
                              then
                                let uu____6477 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6478 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6479 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6480 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6477 uu____6478 uu____6479 uu____6480
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
                                  let uu____6493 =
                                    let uu____6494 =
                                      let uu____6495 =
                                        FStar_Syntax_Syntax.as_arg xexp in
                                      [uu____6495] in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6494 in
                                  uu____6493 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1 in
                              let uu____6499 =
                                let uu____6504 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t) in
                                let uu____6517 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos in
                                let uu____6518 =
                                  FStar_Syntax_Util.lcomp_of_comp cret in
                                let uu____6519 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard) in
                                strengthen_precondition uu____6504 uu____6517
                                  e uu____6518 uu____6519 in
                              match uu____6499 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___120_6523 = x in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___120_6523.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___120_6523.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    } in
                                  let c1 =
                                    let uu____6525 =
                                      FStar_Syntax_Util.lcomp_of_comp c in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____6525
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret) in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1 in
                                  ((let uu____6530 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme in
                                    if uu____6530
                                    then
                                      let uu____6531 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2 in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6531
                                    else ());
                                   c2)))) in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___86_6541  ->
                             match uu___86_6541 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6544 -> [])) in
                   let lc1 =
                     let uu____6546 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     FStar_Syntax_Syntax.mk_lcomp uu____6546 t flags1
                       strengthen in
                   let g2 =
                     let uu___121_6548 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___121_6548.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___121_6548.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___121_6548.FStar_TypeChecker_Env.implicits)
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
        let uu____6571 =
          let uu____6572 =
            let uu____6573 =
              let uu____6574 =
                let uu____6575 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6575 in
              [uu____6574] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6573 in
          uu____6572 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6571 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6582 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6582
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6600 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6615 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6644)::(ens,uu____6646)::uu____6647 ->
                    let uu____6676 =
                      let uu____6679 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6679 in
                    let uu____6680 =
                      let uu____6681 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6681 in
                    (uu____6676, uu____6680)
                | uu____6684 ->
                    let uu____6693 =
                      let uu____6698 =
                        let uu____6699 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6699 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6698) in
                    FStar_Errors.raise_error uu____6693
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6715)::uu____6716 ->
                    let uu____6735 =
                      let uu____6740 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6740 in
                    (match uu____6735 with
                     | (us_r,uu____6772) ->
                         let uu____6773 =
                           let uu____6778 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6778 in
                         (match uu____6773 with
                          | (us_e,uu____6810) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6813 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6813
                                  us_r in
                              let as_ens =
                                let uu____6815 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6815
                                  us_e in
                              let req =
                                let uu____6819 =
                                  let uu____6820 =
                                    let uu____6821 =
                                      let uu____6832 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6832] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6821 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6820 in
                                uu____6819 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6850 =
                                  let uu____6851 =
                                    let uu____6852 =
                                      let uu____6863 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6863] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6852 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6851 in
                                uu____6850 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6878 =
                                let uu____6881 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6881 in
                              let uu____6882 =
                                let uu____6883 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6883 in
                              (uu____6878, uu____6882)))
                | uu____6886 -> failwith "Impossible"))
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
      (let uu____6912 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6912
       then
         let uu____6913 = FStar_Syntax_Print.term_to_string tm in
         let uu____6914 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6913 uu____6914
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
        (let uu____6932 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6932
         then
           let uu____6933 = FStar_Syntax_Print.term_to_string tm in
           let uu____6934 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6933
             uu____6934
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6939 =
      let uu____6940 =
        let uu____6941 = FStar_Syntax_Subst.compress t in
        uu____6941.FStar_Syntax_Syntax.n in
      match uu____6940 with
      | FStar_Syntax_Syntax.Tm_app uu____6944 -> false
      | uu____6959 -> true in
    if uu____6939
    then t
    else
      (let uu____6961 = FStar_Syntax_Util.head_and_args t in
       match uu____6961 with
       | (head1,args) ->
           let uu____6998 =
             let uu____6999 =
               let uu____7000 = FStar_Syntax_Subst.compress head1 in
               uu____7000.FStar_Syntax_Syntax.n in
             match uu____6999 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7003 -> false in
           if uu____6998
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7025 ->
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
             let uu____7062 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____7062 with
             | (formals,uu____7076) ->
                 let n_implicits =
                   let uu____7094 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7170  ->
                             match uu____7170 with
                             | (uu____7177,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7094 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7308 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7308 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7332 =
                     let uu____7337 =
                       let uu____7338 = FStar_Util.string_of_int n_expected in
                       let uu____7345 = FStar_Syntax_Print.term_to_string e in
                       let uu____7346 = FStar_Util.string_of_int n_available in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7338 uu____7345 uu____7346 in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7337) in
                   let uu____7353 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error uu____7332 uu____7353
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___87_7374 =
             match uu___87_7374 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7404 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7404 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7513) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7556,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7589 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7589 with
                           | (v1,uu____7629,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7646 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7646 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7739 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7739)))
                      | (uu____7766,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7812 =
                      let uu____7839 = inst_n_binders t in
                      aux [] uu____7839 bs1 in
                    (match uu____7812 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7910) -> (e, torig, guard)
                          | (uu____7941,[]) when
                              let uu____7972 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7972 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7973 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8005 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____8020 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____8028 =
      let uu____8031 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____8031
        (FStar_List.map
           (fun u  ->
              let uu____8041 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____8041 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____8028 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____8058 = FStar_Util.set_is_empty x in
      if uu____8058
      then []
      else
        (let s =
           let uu____8065 =
             let uu____8068 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____8068 in
           FStar_All.pipe_right uu____8065 FStar_Util.set_elements in
         (let uu____8076 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____8076
          then
            let uu____8077 =
              let uu____8078 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____8078 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8077
          else ());
         (let r =
            let uu____8085 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8085 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8100 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8100
                     then
                       let uu____8101 =
                         let uu____8102 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8102 in
                       let uu____8103 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8104 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8101 uu____8103 uu____8104
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
        let uu____8126 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8126 FStar_Util.fifo_set_elements in
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
        | ([],uu____8158) -> generalized_univ_names
        | (uu____8165,[]) -> explicit_univ_names
        | uu____8172 ->
            let uu____8181 =
              let uu____8186 =
                let uu____8187 = FStar_Syntax_Print.term_to_string t in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8187 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8186) in
            FStar_Errors.raise_error uu____8181 t.FStar_Syntax_Syntax.pos
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
      (let uu____8204 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8204
       then
         let uu____8205 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8205
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8211 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8211
        then
          let uu____8212 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8212
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
        let uu____8282 =
          let uu____8283 =
            FStar_Util.for_all
              (fun uu____8296  ->
                 match uu____8296 with
                 | (uu____8305,uu____8306,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8283 in
        if uu____8282
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8352 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8352
              then
                let uu____8353 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8353
              else ());
             (let c1 =
                let uu____8356 = FStar_TypeChecker_Env.should_verify env in
                if uu____8356
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
              (let uu____8359 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8359
               then
                 let uu____8360 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8360
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8421 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8421 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8551 =
             match uu____8551 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8617 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8617
                   then
                     let uu____8618 =
                       let uu____8619 =
                         let uu____8622 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8622
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8619
                         (FStar_String.concat ", ") in
                     let uu____8649 =
                       let uu____8650 =
                         let uu____8653 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8653
                           (FStar_List.map
                              (fun uu____8681  ->
                                 match uu____8681 with
                                 | (u,t2) ->
                                     let uu____8688 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8689 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8688 uu____8689)) in
                       FStar_All.pipe_right uu____8650
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8618
                       uu____8649
                   else ());
                  (let univs2 =
                     let uu____8696 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8719  ->
                            match uu____8719 with
                            | (uu____8728,t2) ->
                                let uu____8730 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8730)
                       univs1 uu____8696 in
                   let uvs = gen_uvars uvt in
                   (let uu____8753 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8753
                    then
                      let uu____8754 =
                        let uu____8755 =
                          let uu____8758 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8758
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8755
                          (FStar_String.concat ", ") in
                      let uu____8785 =
                        let uu____8786 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8818  ->
                                  match uu____8818 with
                                  | (u,t2) ->
                                      let uu____8825 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8826 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8825 uu____8826)) in
                        FStar_All.pipe_right uu____8786
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8754
                        uu____8785
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8856 =
             let uu____8889 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8889 in
           match uu____8856 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9007 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____9007
                 then ()
                 else
                   (let uu____9009 = lec_hd in
                    match uu____9009 with
                    | (lb1,uu____9017,uu____9018) ->
                        let uu____9019 = lec2 in
                        (match uu____9019 with
                         | (lb2,uu____9027,uu____9028) ->
                             let msg =
                               let uu____9030 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9031 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9030 uu____9031 in
                             let uu____9032 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9032)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9143  ->
                           match uu____9143 with
                           | (u,uu____9151) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9173  ->
                                       match uu____9173 with
                                       | (u',uu____9181) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9186 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9186
                 then ()
                 else
                   (let uu____9188 = lec_hd in
                    match uu____9188 with
                    | (lb1,uu____9196,uu____9197) ->
                        let uu____9198 = lec2 in
                        (match uu____9198 with
                         | (lb2,uu____9206,uu____9207) ->
                             let msg =
                               let uu____9209 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9210 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9209 uu____9210 in
                             let uu____9211 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9211)) in
               let lecs1 =
                 let uu____9221 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9280 = univs_and_uvars_of_lec this_lec in
                        match uu____9280 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9221 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9433 = lec_hd in
                   match uu____9433 with
                   | (lbname,e,c) ->
                       let uu____9443 =
                         let uu____9448 =
                           let uu____9449 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____9450 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____9451 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9449 uu____9450 uu____9451 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9448) in
                       let uu____9452 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____9443 uu____9452 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9482  ->
                         match uu____9482 with
                         | (u,k) ->
                             let uu____9495 = FStar_Syntax_Unionfind.find u in
                             (match uu____9495 with
                              | FStar_Pervasives_Native.Some uu____9504 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9511 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9515 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9515 with
                                   | (bs,kres) ->
                                       ((let uu____9553 =
                                           let uu____9554 =
                                             let uu____9557 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9557 in
                                           uu____9554.FStar_Syntax_Syntax.n in
                                         match uu____9553 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9558 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9562 =
                                               let uu____9563 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9563 in
                                             if uu____9562
                                             then fail kres
                                             else ()
                                         | uu____9565 -> fail kres);
                                        (let a =
                                           let uu____9567 =
                                             let uu____9570 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9570 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9567 kres in
                                         let t =
                                           let uu____9574 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9574
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
                      (fun uu____9693  ->
                         match uu____9693 with
                         | (lbname,e,c) ->
                             let uu____9739 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9808 ->
                                   let uu____9823 = (e, c) in
                                   (match uu____9823 with
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
                                                (fun uu____9860  ->
                                                   match uu____9860 with
                                                   | (x,uu____9868) ->
                                                       let uu____9873 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9873)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9883 =
                                                let uu____9884 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9884 in
                                              if uu____9883
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
                                          let uu____9892 =
                                            let uu____9893 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9893.FStar_Syntax_Syntax.n in
                                          match uu____9892 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9916 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9916 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9931 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9933 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9933, gen_tvars)) in
                             (match uu____9739 with
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
        (let uu____10079 = Obj.magic () in ());
        (let uu____10081 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____10081
         then
           let uu____10082 =
             let uu____10083 =
               FStar_List.map
                 (fun uu____10096  ->
                    match uu____10096 with
                    | (lb,uu____10104,uu____10105) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____10083 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____10082
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10126  ->
                match uu____10126 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10155 = gen env is_rec lecs in
           match uu____10155 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10254  ->
                       match uu____10254 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10316 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10316
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10360  ->
                           match uu____10360 with
                           | (l,us,e,c,gvs) ->
                               let uu____10394 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10395 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10396 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10397 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10398 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10394 uu____10395 uu____10396
                                 uu____10397 uu____10398))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10439  ->
                match uu____10439 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10483 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10483, t, c, gvs)) univnames_lecs
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
              (let uu____10526 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10526 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10532 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10532) in
          let is_var e1 =
            let uu____10539 =
              let uu____10540 = FStar_Syntax_Subst.compress e1 in
              uu____10540.FStar_Syntax_Syntax.n in
            match uu____10539 with
            | FStar_Syntax_Syntax.Tm_name uu____10543 -> true
            | uu____10544 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___122_10560 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___122_10560.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___122_10560.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10561 -> e2 in
          let env2 =
            let uu___123_10563 = env1 in
            let uu____10564 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___123_10563.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___123_10563.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___123_10563.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___123_10563.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___123_10563.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___123_10563.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___123_10563.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___123_10563.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___123_10563.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___123_10563.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___123_10563.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___123_10563.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___123_10563.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___123_10563.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___123_10563.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10564;
              FStar_TypeChecker_Env.is_iface =
                (uu___123_10563.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___123_10563.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___123_10563.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___123_10563.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___123_10563.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___123_10563.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___123_10563.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___123_10563.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___123_10563.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___123_10563.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___123_10563.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___123_10563.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___123_10563.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___123_10563.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___123_10563.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___123_10563.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___123_10563.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___123_10563.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10565 = check env2 t1 t2 in
          match uu____10565 with
          | FStar_Pervasives_Native.None  ->
              let uu____10572 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____10577 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____10572 uu____10577
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10584 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10584
                then
                  let uu____10585 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10585
                else ());
               (let uu____10587 = decorate e t2 in (uu____10587, g)))
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
        let uu____10615 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10615
        then
          let uu____10620 = discharge g1 in
          let uu____10621 = FStar_Syntax_Syntax.lcomp_comp lc in
          (uu____10620, uu____10621)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10628 =
               let uu____10629 =
                 let uu____10630 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10630 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10629
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10628
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10632 = destruct_comp c1 in
           match uu____10632 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10649 = FStar_TypeChecker_Env.get_range env in
                 let uu____10650 =
                   let uu____10651 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10652 =
                     let uu____10653 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10654 =
                       let uu____10657 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10657] in
                     uu____10653 :: uu____10654 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10651 uu____10652 in
                 uu____10650 FStar_Pervasives_Native.None uu____10649 in
               ((let uu____10661 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10661
                 then
                   let uu____10662 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10662
                 else ());
                (let g2 =
                   let uu____10665 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10665 in
                 let uu____10666 = discharge g2 in
                 let uu____10667 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10666, uu____10667))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___88_10691 =
        match uu___88_10691 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10699)::[] -> f fst1
        | uu____10716 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10721 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10721
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10730 =
          let uu____10733 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10733 in
        FStar_All.pipe_right uu____10730
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10744 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10744
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___89_10758 =
        match uu___89_10758 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10766)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10785)::[] ->
            let uu____10814 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10814
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10819 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10829 =
          let uu____10836 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10836) in
        let uu____10841 =
          let uu____10850 =
            let uu____10857 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10857) in
          let uu____10862 =
            let uu____10871 =
              let uu____10878 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10878) in
            let uu____10883 =
              let uu____10892 =
                let uu____10899 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10899) in
              let uu____10904 =
                let uu____10913 =
                  let uu____10920 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10920) in
                [uu____10913; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10892 :: uu____10904 in
            uu____10871 :: uu____10883 in
          uu____10850 :: uu____10862 in
        uu____10829 :: uu____10841 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10971 =
            FStar_Util.find_map table
              (fun uu____10984  ->
                 match uu____10984 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11001 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____11001
                     else FStar_Pervasives_Native.None) in
          (match uu____10971 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11004 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____11008 =
      let uu____11009 = FStar_Syntax_Util.un_uinst l in
      uu____11009.FStar_Syntax_Syntax.n in
    match uu____11008 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11013 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11037)::uu____11038 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11049 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____11056,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11057))::uu____11058 -> bs
      | uu____11075 ->
          let uu____11076 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____11076 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11080 =
                 let uu____11081 = FStar_Syntax_Subst.compress t in
                 uu____11081.FStar_Syntax_Syntax.n in
               (match uu____11080 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11085) ->
                    let uu____11102 =
                      FStar_Util.prefix_until
                        (fun uu___90_11142  ->
                           match uu___90_11142 with
                           | (uu____11149,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11150)) ->
                               false
                           | uu____11153 -> true) bs' in
                    (match uu____11102 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11188,uu____11189) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11261,uu____11262) ->
                         let uu____11335 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11353  ->
                                   match uu____11353 with
                                   | (x,uu____11361) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11335
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11408  ->
                                     match uu____11408 with
                                     | (x,i) ->
                                         let uu____11427 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11427, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11437 -> bs))
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
          let uu____11469 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11469
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
        (let uu____11492 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11492
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11494 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11494))
         else ());
        (let fv =
           let uu____11497 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11497
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
         let uu____11505 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___124_11511 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___124_11511.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___124_11511.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___124_11511.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___124_11511.FStar_Syntax_Syntax.sigattrs)
           }), uu____11505))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___91_11521 =
        match uu___91_11521 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11522 -> false in
      let reducibility uu___92_11526 =
        match uu___92_11526 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11527 -> false in
      let assumption uu___93_11531 =
        match uu___93_11531 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11532 -> false in
      let reification uu___94_11536 =
        match uu___94_11536 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11537 -> true
        | uu____11538 -> false in
      let inferred uu___95_11542 =
        match uu___95_11542 with
        | FStar_Syntax_Syntax.Discriminator uu____11543 -> true
        | FStar_Syntax_Syntax.Projector uu____11544 -> true
        | FStar_Syntax_Syntax.RecordType uu____11549 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11558 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11567 -> false in
      let has_eq uu___96_11571 =
        match uu___96_11571 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11572 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11632 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11637 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11641 =
        let uu____11642 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___97_11646  ->
                  match uu___97_11646 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11647 -> false)) in
        FStar_All.pipe_right uu____11642 Prims.op_Negation in
      if uu____11641
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11660 =
            let uu____11665 =
              let uu____11666 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11666 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11665) in
          FStar_Errors.raise_error uu____11660 r in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11674 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11678 =
            let uu____11679 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11679 in
          if uu____11678 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11684),uu____11685) ->
              ((let uu____11701 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11701
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11705 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11705
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11711 ->
              let uu____11720 =
                let uu____11721 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11721 in
              if uu____11720 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11727 ->
              let uu____11734 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11734 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11738 ->
              let uu____11745 =
                let uu____11746 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11746 in
              if uu____11745 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11752 ->
              let uu____11753 =
                let uu____11754 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11754 in
              if uu____11753 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11760 ->
              let uu____11761 =
                let uu____11762 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11762 in
              if uu____11761 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11768 ->
              let uu____11781 =
                let uu____11782 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11782 in
              if uu____11781 then err'1 () else ()
          | uu____11788 -> ()))
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
                          let uu____11851 =
                            let uu____11854 =
                              let uu____11855 =
                                let uu____11862 =
                                  let uu____11863 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11863 in
                                (uu____11862, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11855 in
                            FStar_Syntax_Syntax.mk uu____11854 in
                          uu____11851 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11904  ->
                                  match uu____11904 with
                                  | (x,imp) ->
                                      let uu____11915 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11915, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11917 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11917 in
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
                             let uu____11926 =
                               let uu____11927 =
                                 let uu____11928 =
                                   let uu____11929 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11930 =
                                     let uu____11931 =
                                       let uu____11932 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11932 in
                                     [uu____11931] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11929
                                     uu____11930 in
                                 uu____11928 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11927 in
                             FStar_Syntax_Util.refine x uu____11926 in
                           let uu____11935 =
                             let uu___125_11936 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___125_11936.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___125_11936.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11935) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11951 =
                          FStar_List.map
                            (fun uu____11973  ->
                               match uu____11973 with
                               | (x,uu____11985) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11951 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12034  ->
                                match uu____12034 with
                                | (x,uu____12046) ->
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
                             (let uu____12060 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12060)
                               ||
                               (let uu____12062 =
                                  let uu____12063 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____12063.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____12062) in
                           let quals =
                             let uu____12067 =
                               let uu____12070 =
                                 let uu____12073 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____12073
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____12077 =
                                 FStar_List.filter
                                   (fun uu___98_12081  ->
                                      match uu___98_12081 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12082 -> false) iquals in
                               FStar_List.append uu____12070 uu____12077 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12067 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12103 =
                                 let uu____12104 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12104 in
                               FStar_Syntax_Syntax.mk_Total uu____12103 in
                             let uu____12105 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12105 in
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
                           (let uu____12108 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12108
                            then
                              let uu____12109 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12109
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
                                             fun uu____12162  ->
                                               match uu____12162 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12186 =
                                                       let uu____12189 =
                                                         let uu____12190 =
                                                           let uu____12197 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12197,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12190 in
                                                       pos uu____12189 in
                                                     (uu____12186, b)
                                                   else
                                                     (let uu____12201 =
                                                        let uu____12204 =
                                                          let uu____12205 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12205 in
                                                        pos uu____12204 in
                                                      (uu____12201, b)))) in
                                   let pat_true =
                                     let uu____12223 =
                                       let uu____12226 =
                                         let uu____12227 =
                                           let uu____12240 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12240, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12227 in
                                       pos uu____12226 in
                                     (uu____12223,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12274 =
                                       let uu____12277 =
                                         let uu____12278 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12278 in
                                       pos uu____12277 in
                                     (uu____12274,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12290 =
                                     let uu____12293 =
                                       let uu____12294 =
                                         let uu____12317 =
                                           let uu____12320 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12321 =
                                             let uu____12324 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12324] in
                                           uu____12320 :: uu____12321 in
                                         (arg_exp, uu____12317) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12294 in
                                     FStar_Syntax_Syntax.mk uu____12293 in
                                   uu____12290 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12331 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12331
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
                                let uu____12339 =
                                  let uu____12344 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12344 in
                                let uu____12345 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12339;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12345
                                } in
                              let impl =
                                let uu____12349 =
                                  let uu____12350 =
                                    let uu____12357 =
                                      let uu____12360 =
                                        let uu____12361 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12361
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12360] in
                                    ((false, [lb]), uu____12357) in
                                  FStar_Syntax_Syntax.Sig_let uu____12350 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12349;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12379 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12379
                               then
                                 let uu____12380 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12380
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
                                fun uu____12422  ->
                                  match uu____12422 with
                                  | (a,uu____12428) ->
                                      let uu____12429 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12429 with
                                       | (field_name,uu____12435) ->
                                           let field_proj_tm =
                                             let uu____12437 =
                                               let uu____12438 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12438 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12437 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12455 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12487  ->
                                    match uu____12487 with
                                    | (x,uu____12495) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12497 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12497 with
                                         | (field_name,uu____12505) ->
                                             let t =
                                               let uu____12507 =
                                                 let uu____12508 =
                                                   let uu____12511 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12511 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12508 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12507 in
                                             let only_decl =
                                               (let uu____12515 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12515)
                                                 ||
                                                 (let uu____12517 =
                                                    let uu____12518 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12518.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12517) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12532 =
                                                   FStar_List.filter
                                                     (fun uu___99_12536  ->
                                                        match uu___99_12536
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12537 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12532
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___100_12550  ->
                                                         match uu___100_12550
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12551 ->
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
                                             ((let uu____12570 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12570
                                               then
                                                 let uu____12571 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12571
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
                                                           fun uu____12619 
                                                             ->
                                                             match uu____12619
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12643
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12643,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12659
                                                                    =
                                                                    let uu____12662
                                                                    =
                                                                    let uu____12663
                                                                    =
                                                                    let uu____12670
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12670,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12663 in
                                                                    pos
                                                                    uu____12662 in
                                                                    (uu____12659,
                                                                    b))
                                                                   else
                                                                    (let uu____12674
                                                                    =
                                                                    let uu____12677
                                                                    =
                                                                    let uu____12678
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12678 in
                                                                    pos
                                                                    uu____12677 in
                                                                    (uu____12674,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12694 =
                                                     let uu____12697 =
                                                       let uu____12698 =
                                                         let uu____12711 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12711,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12698 in
                                                     pos uu____12697 in
                                                   let uu____12720 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12694,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12720) in
                                                 let body =
                                                   let uu____12732 =
                                                     let uu____12735 =
                                                       let uu____12736 =
                                                         let uu____12759 =
                                                           let uu____12762 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12762] in
                                                         (arg_exp,
                                                           uu____12759) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12736 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12735 in
                                                   uu____12732
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12770 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12770
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
                                                   let uu____12777 =
                                                     let uu____12782 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12782 in
                                                   let uu____12783 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12777;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12783
                                                   } in
                                                 let impl =
                                                   let uu____12787 =
                                                     let uu____12788 =
                                                       let uu____12795 =
                                                         let uu____12798 =
                                                           let uu____12799 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12799
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12798] in
                                                       ((false, [lb]),
                                                         uu____12795) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12788 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12787;
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
                                                 (let uu____12817 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12817
                                                  then
                                                    let uu____12818 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12818
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12455 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12858) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12863 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12863 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12885 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12885 with
                    | (formals,uu____12901) ->
                        let uu____12918 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12950 =
                                   let uu____12951 =
                                     let uu____12952 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12952 in
                                   FStar_Ident.lid_equals typ_lid uu____12951 in
                                 if uu____12950
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12971,uvs',tps,typ0,uu____12975,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12994 -> failwith "Impossible"
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
                        (match uu____12918 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____13067 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____13067 with
                              | (indices,uu____13083) ->
                                  let refine_domain =
                                    let uu____13101 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___101_13106  ->
                                              match uu___101_13106 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13107 -> true
                                              | uu____13116 -> false)) in
                                    if uu____13101
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___102_13124 =
                                      match uu___102_13124 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13127,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13139 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13140 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13140 with
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
                                    let uu____13151 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13151 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13216  ->
                                               fun uu____13217  ->
                                                 match (uu____13216,
                                                         uu____13217)
                                                 with
                                                 | ((x,uu____13235),(x',uu____13237))
                                                     ->
                                                     let uu____13246 =
                                                       let uu____13253 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13253) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13246) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13254 -> []