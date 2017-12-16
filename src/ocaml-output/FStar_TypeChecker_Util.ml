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
  fun uu___275_93  ->
    match uu___275_93 with
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
                     let uu___296_257 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u in
                         (reason, env, uu____286, t, k, r) in
                       [uu____273] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___296_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___296_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___296_257.FStar_TypeChecker_Env.univ_ineqs);
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
                            ((let uu___297_497 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___297_497.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___297_497.FStar_Syntax_Syntax.index);
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
                ((let uu___298_1126 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___298_1126.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___298_1126.FStar_Syntax_Syntax.index);
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
                       let uu___299_1237 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___299_1237.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___299_1237.FStar_Syntax_Syntax.index);
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
                            let uu___300_1269 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___300_1269.FStar_Syntax_Syntax.p)
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
                       (let uu___301_1991 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___301_1991.FStar_Syntax_Syntax.p)
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
                          let uu___302_2574 = p1 in
                          let uu____2577 =
                            let uu____2578 =
                              let uu____2591 = aux f pats1 in
                              (fv, uu____2591) in
                            FStar_Syntax_Syntax.Pat_cons uu____2578 in
                          {
                            FStar_Syntax_Syntax.v = uu____2577;
                            FStar_Syntax_Syntax.p =
                              (uu___302_2574.FStar_Syntax_Syntax.p)
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
                  let uu___303_2860 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___303_2860.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___303_2860.FStar_Syntax_Syntax.index);
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
                  let uu___304_2871 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___304_2871.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___304_2871.FStar_Syntax_Syntax.index);
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
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3946)::[] -> wp
      | uu____3963 ->
          let uu____3972 =
            let uu____3973 =
              let uu____3974 =
                FStar_List.map
                  (fun uu____3984  ->
                     match uu____3984 with
                     | (x,uu____3990) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3974 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3973 in
          failwith uu____3972 in
    let uu____3995 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3995, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4009 = destruct_comp c in
        match uu____4009 with
        | (u,uu____4017,wp) ->
            let uu____4019 =
              let uu____4028 =
                let uu____4029 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____4029 in
              [uu____4028] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4019;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4039 =
          let uu____4046 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____4047 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____4046 uu____4047 in
        match uu____4039 with | (m,uu____4049,uu____4050) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4060 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____4060
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
        let uu____4097 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____4097 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4134 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4134 with
             | (a,kwp) ->
                 let uu____4165 = destruct_comp m1 in
                 let uu____4172 = destruct_comp m2 in
                 ((md, a, kwp), uu____4165, uu____4172))
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
            let uu____4234 =
              let uu____4235 =
                let uu____4244 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4244] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4235;
                FStar_Syntax_Syntax.flags = flags1
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4234
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
      let uu___305_4283 = lc in
      let uu____4284 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___305_4283.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4284;
        FStar_Syntax_Syntax.cflags =
          (uu___305_4283.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4289  ->
             let uu____4290 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4290)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4294 =
      let uu____4295 = FStar_Syntax_Subst.compress t in
      uu____4295.FStar_Syntax_Syntax.n in
    match uu____4294 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4298 -> true
    | uu____4311 -> false
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
              let uu____4349 =
                let uu____4350 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4350 in
              if uu____4349
              then f
              else (let uu____4352 = reason1 () in label uu____4352 r f)
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
            let uu___306_4363 = g in
            let uu____4364 =
              let uu____4365 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4365 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4364;
              FStar_TypeChecker_Env.deferred =
                (uu___306_4363.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___306_4363.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___306_4363.FStar_TypeChecker_Env.implicits)
            }
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4379 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4379
        then c
        else
          (let uu____4381 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4381
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4420 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4420] in
                       let us =
                         let uu____4424 =
                           let uu____4427 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4427] in
                         u_res :: uu____4424 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4431 =
                         let uu____4432 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4433 =
                           let uu____4434 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4435 =
                             let uu____4438 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4439 =
                               let uu____4442 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4442] in
                             uu____4438 :: uu____4439 in
                           uu____4434 :: uu____4435 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4432 uu____4433 in
                       uu____4431 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4446 = destruct_comp c1 in
              match uu____4446 with
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
        let close1 uu____4474 =
          let uu____4475 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4475 in
        let uu___307_4476 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___307_4476.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___307_4476.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___307_4476.FStar_Syntax_Syntax.cflags);
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
          let uu____4487 =
            let uu____4488 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4488 in
          if uu____4487
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let uu____4490 = FStar_Syntax_Util.is_unit t in
             if uu____4490
             then
               FStar_Syntax_Syntax.mk_Total' t
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
             else
               (let m =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Parser_Const.effect_PURE_lid in
                let u_t = env.FStar_TypeChecker_Env.universe_of env t in
                let wp =
                  let uu____4495 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____4495
                  then FStar_Syntax_Syntax.tun
                  else
                    (let uu____4497 =
                       FStar_TypeChecker_Env.wp_signature env
                         FStar_Parser_Const.effect_PURE_lid in
                     match uu____4497 with
                     | (a,kwp) ->
                         let k =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (a, t)] kwp in
                         let uu____4505 =
                           let uu____4506 =
                             let uu____4507 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                             let uu____4508 =
                               let uu____4509 = FStar_Syntax_Syntax.as_arg t in
                               let uu____4510 =
                                 let uu____4513 =
                                   FStar_Syntax_Syntax.as_arg v1 in
                                 [uu____4513] in
                               uu____4509 :: uu____4510 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____4507
                               uu____4508 in
                           uu____4506 FStar_Pervasives_Native.None
                             v1.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.NoFullNorm] env
                           uu____4505) in
                mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
        (let uu____4517 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4517
         then
           let uu____4518 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4519 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4520 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4518
             uu____4519 uu____4520
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
          fun uu____4538  ->
            match uu____4538 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4551 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4551
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4554 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4556 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4557 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4554 uu____4556 bstr uu____4557
                  else ());
                 (let bind_it uu____4562 =
                    let uu____4563 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4563
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4573 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4573
                        then
                          let uu____4574 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4576 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4577 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4578 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4579 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4574 uu____4576 uu____4577 uu____4578
                            uu____4579
                        else ());
                       (let aux uu____4594 =
                          let uu____4595 = FStar_Syntax_Util.is_trivial_wp c1 in
                          if uu____4595
                          then
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Util.Inl (c2, "trivial no binder")
                            | FStar_Pervasives_Native.Some uu____4624 ->
                                let uu____4625 =
                                  FStar_Syntax_Util.is_ml_comp c2 in
                                (if uu____4625
                                 then FStar_Util.Inl (c2, "trivial ml")
                                 else
                                   FStar_Util.Inr
                                     "c1 trivial; but c2 is not ML")
                          else
                            (let uu____4652 =
                               (FStar_Syntax_Util.is_ml_comp c1) &&
                                 (FStar_Syntax_Util.is_ml_comp c2) in
                             if uu____4652
                             then FStar_Util.Inl (c2, "both ml")
                             else
                               FStar_Util.Inr
                                 "c1 not trivial, and both are not ML") in
                        let subst_c2 reason =
                          match (e1opt, b) with
                          | (FStar_Pervasives_Native.Some
                             e,FStar_Pervasives_Native.Some x) ->
                              let uu____4708 =
                                let uu____4713 =
                                  FStar_Syntax_Subst.subst_comp
                                    [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                (uu____4713, reason) in
                              FStar_Util.Inl uu____4708
                          | uu____4718 -> aux () in
                        let try_simplify uu____4740 =
                          let rec maybe_close t x c =
                            let uu____4751 =
                              let uu____4752 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4752.FStar_Syntax_Syntax.n in
                            match uu____4751 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4756) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4762 -> c in
                          let uu____4763 =
                            let uu____4764 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4764 in
                          if uu____4763
                          then
                            let uu____4777 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4777
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4797 =
                                  FStar_TypeChecker_Env.get_range env in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                    "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                  uu____4797))
                          else
                            (let uu____4809 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4809
                             then subst_c2 "both total"
                             else
                               (let uu____4821 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4821
                                then
                                  let uu____4832 =
                                    let uu____4837 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4837, "both gtot") in
                                  FStar_Util.Inl uu____4832
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4863 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4865 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4865) in
                                       if uu____4863
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___308_4878 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___308_4878.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___308_4878.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4879 =
                                           let uu____4884 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4884, "c1 Tot") in
                                         FStar_Util.Inl uu____4879
                                       else aux ()
                                   | uu____4890 -> aux ()))) in
                        let uu____4899 = try_simplify () in
                        match uu____4899 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4923 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4923
                              then
                                let uu____4924 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4925 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4926 =
                                  FStar_Syntax_Print.comp_to_string c in
                                let uu____4927 =
                                  FStar_Syntax_Print.lid_to_string joined_eff in
                                FStar_Util.print5
                                  "Simplified (because %s) bind c1: %s\n\nc2: %s\n\nto c: %s\n\nWith effect lid: %s\n\n"
                                  reason uu____4924 uu____4925 uu____4926
                                  uu____4927
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1 in
                            let uu____4937 = destruct_comp c1_typ in
                            (match uu____4937 with
                             | (u_res_t1,res_t1,uu____4946) ->
                                 let should_inline_c1 uu____4950 =
                                   ((FStar_Syntax_Util.is_pure_or_ghost_comp
                                       c1)
                                      &&
                                      (let uu____4952 =
                                         FStar_Syntax_Util.is_unit res_t1 in
                                       Prims.op_Negation uu____4952))
                                     &&
                                     (match e1opt with
                                      | FStar_Pervasives_Native.Some e1 ->
                                          let uu____4964 =
                                            FStar_Syntax_Util.head_and_args'
                                              e1 in
                                          (match uu____4964 with
                                           | (head1,uu____4978) ->
                                               let uu____4995 =
                                                 let uu____4996 =
                                                   FStar_Syntax_Util.un_uinst
                                                     head1 in
                                                 uu____4996.FStar_Syntax_Syntax.n in
                                               (match uu____4995 with
                                                | FStar_Syntax_Syntax.Tm_fvar
                                                    fv ->
                                                    let uu____5000 =
                                                      let uu____5021 =
                                                        FStar_Syntax_Syntax.lid_of_fv
                                                          fv in
                                                      FStar_TypeChecker_Env.lookup_qname
                                                        env uu____5021 in
                                                    (match uu____5000 with
                                                     | FStar_Pervasives_Native.Some
                                                         (FStar_Util.Inr
                                                          (se,uu____5023),uu____5024)
                                                         ->
                                                         Prims.op_Negation
                                                           (FStar_List.existsb
                                                              (fun
                                                                 uu___276_5072
                                                                  ->
                                                                 match uu___276_5072
                                                                 with
                                                                 | FStar_Syntax_Syntax.Irreducible
                                                                     -> true
                                                                 | FStar_Syntax_Syntax.Assumption
                                                                     -> true
                                                                 | uu____5073
                                                                    -> false)
                                                              se.FStar_Syntax_Syntax.sigquals)
                                                     | uu____5074 -> true)
                                                | FStar_Syntax_Syntax.Tm_let
                                                    ((true ,uu____5095),uu____5096)
                                                    -> false
                                                | uu____5111 -> true))
                                      | uu____5112 -> false) in
                                 let c21 =
                                   let uu____5116 = should_inline_c1 () in
                                   if uu____5116
                                   then
                                     match (e1opt, b) with
                                     | (FStar_Pervasives_Native.Some
                                        e,FStar_Pervasives_Native.Some bv) ->
                                         let uu____5127 =
                                           subst_c2 "inline all pure" in
                                         (match uu____5127 with
                                          | FStar_Util.Inl (c21,uu____5137)
                                              ->
                                              let c2_typ =
                                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                                  env c21 in
                                              let uu____5143 =
                                                destruct_comp c2_typ in
                                              (match uu____5143 with
                                               | (u_res_t,res_t,wp) ->
                                                   let md =
                                                     FStar_TypeChecker_Env.get_effect_decl
                                                       env
                                                       c2_typ.FStar_Syntax_Syntax.effect_name in
                                                   let wp1 =
                                                     if
                                                       Prims.op_Negation
                                                         (FStar_List.existsb
                                                            (fun
                                                               uu___277_5160 
                                                               ->
                                                               match uu___277_5160
                                                               with
                                                               | FStar_Syntax_Syntax.RETURN
                                                                    -> true
                                                               | FStar_Syntax_Syntax.PARTIAL_RETURN
                                                                    -> true
                                                               | uu____5161
                                                                   -> false)
                                                            c1_typ.FStar_Syntax_Syntax.flags)
                                                     then
                                                       let uu____5162 =
                                                         let uu____5163 =
                                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                                             [u_res_t] env md
                                                             md.FStar_Syntax_Syntax.assume_p in
                                                         let uu____5164 =
                                                           let uu____5165 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               res_t in
                                                           let uu____5166 =
                                                             let uu____5169 =
                                                               let uu____5170
                                                                 =
                                                                 let uu____5171
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    bv in
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   u_res_t1
                                                                   res_t1
                                                                   uu____5171
                                                                   e in
                                                               FStar_Syntax_Syntax.as_arg
                                                                 uu____5170 in
                                                             let uu____5172 =
                                                               let uu____5175
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   wp in
                                                               [uu____5175] in
                                                             uu____5169 ::
                                                               uu____5172 in
                                                           uu____5165 ::
                                                             uu____5166 in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____5163
                                                           uu____5164 in
                                                       uu____5162
                                                         FStar_Pervasives_Native.None
                                                         wp.FStar_Syntax_Syntax.pos
                                                     else wp in
                                                   mk_comp md u_res_t res_t
                                                     wp1
                                                     c2_typ.FStar_Syntax_Syntax.flags)
                                          | FStar_Util.Inr uu____5179 -> c2)
                                     | (uu____5184,uu____5185) -> c2
                                   else c2 in
                                 let uu____5195 =
                                   lift_and_destruct env c1 c21 in
                                 (match uu____5195 with
                                  | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                      ->
                                      let bs =
                                        match b with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5252 =
                                              FStar_Syntax_Syntax.null_binder
                                                t1 in
                                            [uu____5252]
                                        | FStar_Pervasives_Native.Some x ->
                                            let uu____5254 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____5254] in
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
                                        let uu____5267 =
                                          FStar_Syntax_Syntax.as_arg r11 in
                                        let uu____5268 =
                                          let uu____5271 =
                                            FStar_Syntax_Syntax.as_arg t1 in
                                          let uu____5272 =
                                            let uu____5275 =
                                              FStar_Syntax_Syntax.as_arg t2 in
                                            let uu____5276 =
                                              let uu____5279 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wp1 in
                                              let uu____5280 =
                                                let uu____5283 =
                                                  let uu____5284 = mk_lam wp2 in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____5284 in
                                                [uu____5283] in
                                              uu____5279 :: uu____5280 in
                                            uu____5275 :: uu____5276 in
                                          uu____5271 :: uu____5272 in
                                        uu____5267 :: uu____5268 in
                                      let wp =
                                        let uu____5288 =
                                          let uu____5289 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_t1; u_t2] env md
                                              md.FStar_Syntax_Syntax.bind_wp in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____5289 wp_args in
                                        uu____5288
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
      | uu____5301 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5320 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5324 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5324
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5331 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5331
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5336 = destruct_comp c1 in
                    match uu____5336 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5352 =
                            let uu____5353 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5354 =
                              let uu____5355 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5356 =
                                let uu____5359 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5360 =
                                  let uu____5363 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5363] in
                                uu____5359 :: uu____5360 in
                              uu____5355 :: uu____5356 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5353
                              uu____5354 in
                          uu____5352 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___309_5366 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___309_5366.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___309_5366.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___309_5366.FStar_Syntax_Syntax.cflags);
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
            let uu____5399 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5399
            then (lc, g0)
            else
              ((let uu____5406 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5406
                then
                  let uu____5407 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5408 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5407 uu____5408
                else ());
               (let flags1 =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___278_5418  ->
                          match uu___278_5418 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5421 -> [])) in
                let strengthen uu____5427 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5435 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5435 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         ((let uu____5440 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5440
                           then
                             let uu____5441 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5442 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5441 uu____5442
                           else ());
                          (let c1 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                           let uu____5445 = destruct_comp c1 in
                           match uu____5445 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c1.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5461 =
                                   let uu____5462 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5463 =
                                     let uu____5464 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5465 =
                                       let uu____5468 =
                                         let uu____5469 =
                                           let uu____5470 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5470 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5469 in
                                       let uu____5471 =
                                         let uu____5474 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5474] in
                                       uu____5468 :: uu____5471 in
                                     uu____5464 :: uu____5465 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5462
                                     uu____5463 in
                                 uu____5461 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5478 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5478
                                 then
                                   let uu____5479 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5479
                                 else ());
                                (let c2 = mk_comp md u_res_t res_t wp1 flags1 in
                                 c2))))) in
                let uu____5482 =
                  let uu___310_5483 = lc in
                  let uu____5484 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5485 =
                    let uu____5488 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5490 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5490) in
                    if uu____5488 then flags1 else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5484;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___310_5483.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5485;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5482,
                  (let uu___311_5495 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___311_5495.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___311_5495.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___311_5495.FStar_TypeChecker_Env.implicits)
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
        let uu____5510 =
          let uu____5515 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5516 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5515, uu____5516) in
        match uu____5510 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5525 =
                let uu____5526 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5527 =
                  let uu____5528 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5529 =
                    let uu____5532 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5532] in
                  uu____5528 :: uu____5529 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5526 uu____5527 in
              uu____5525 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5538 =
                let uu____5539 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5540 =
                  let uu____5541 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5542 =
                    let uu____5545 =
                      let uu____5546 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5546 in
                    let uu____5547 =
                      let uu____5550 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5550] in
                    uu____5545 :: uu____5547 in
                  uu____5541 :: uu____5542 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5539 uu____5540 in
              uu____5538 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5556 =
                let uu____5557 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5558 =
                  let uu____5559 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5560 =
                    let uu____5563 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5564 =
                      let uu____5567 =
                        let uu____5568 =
                          let uu____5569 =
                            let uu____5570 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5570] in
                          FStar_Syntax_Util.abs uu____5569 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5568 in
                      [uu____5567] in
                    uu____5563 :: uu____5564 in
                  uu____5559 :: uu____5560 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5557 uu____5558 in
              uu____5556 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5577 = FStar_TypeChecker_Env.get_range env in
              bind uu____5577 env FStar_Pervasives_Native.None
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
          let comp uu____5596 =
            let uu____5597 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5597
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5600 =
                 let uu____5625 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5626 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5625 uu____5626 in
               match uu____5600 with
               | ((md,uu____5628,uu____5629),(u_res_t,res_t,wp_then),
                  (uu____5633,uu____5634,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5672 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5673 =
                       let uu____5674 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5675 =
                         let uu____5676 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5677 =
                           let uu____5680 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5681 =
                             let uu____5684 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5685 =
                               let uu____5688 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5688] in
                             uu____5684 :: uu____5685 in
                           uu____5680 :: uu____5681 in
                         uu____5676 :: uu____5677 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5674 uu____5675 in
                     uu____5673 FStar_Pervasives_Native.None uu____5672 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5694 =
                     let uu____5695 = FStar_Options.split_cases () in
                     uu____5695 > (Prims.parse_int "0") in
                   if uu____5694
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5701 =
                          let uu____5702 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5703 =
                            let uu____5704 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5705 =
                              let uu____5708 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5708] in
                            uu____5704 :: uu____5705 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5702 uu____5703 in
                        uu____5701 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5711 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5711;
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
      let uu____5718 =
        let uu____5719 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5719 in
      FStar_Syntax_Syntax.fvar uu____5718 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5751  ->
                 match uu____5751 with
                 | (uu____5756,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5761 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5763 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5763
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5783 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5784 =
                 let uu____5785 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5786 =
                   let uu____5787 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5788 =
                     let uu____5791 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5792 =
                       let uu____5795 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5796 =
                         let uu____5799 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5799] in
                       uu____5795 :: uu____5796 in
                     uu____5791 :: uu____5792 in
                   uu____5787 :: uu____5788 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5785 uu____5786 in
               uu____5784 FStar_Pervasives_Native.None uu____5783 in
             let default_case =
               let post_k =
                 let uu____5806 =
                   let uu____5813 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5813] in
                 let uu____5814 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5806 uu____5814 in
               let kwp =
                 let uu____5820 =
                   let uu____5827 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5827] in
                 let uu____5828 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5820 uu____5828 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5833 =
                   let uu____5834 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5834] in
                 let uu____5835 =
                   let uu____5836 =
                     let uu____5839 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5839 in
                   let uu____5840 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5836 uu____5840 in
                 FStar_Syntax_Util.abs uu____5833 uu____5835
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
                 (fun uu____5864  ->
                    fun celse  ->
                      match uu____5864 with
                      | (g,cthen) ->
                          let uu____5872 =
                            let uu____5897 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5897 celse in
                          (match uu____5872 with
                           | ((md,uu____5899,uu____5900),(uu____5901,uu____5902,wp_then),
                              (uu____5904,uu____5905,wp_else)) ->
                               let uu____5925 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5925 []))
                 lcases default_case in
             let uu____5926 =
               let uu____5927 = FStar_Options.split_cases () in
               uu____5927 > (Prims.parse_int "0") in
             if uu____5926
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5931 = destruct_comp comp1 in
                match uu____5931 with
                | (uu____5938,uu____5939,wp) ->
                    let wp1 =
                      let uu____5944 =
                        let uu____5945 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5946 =
                          let uu____5947 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5948 =
                            let uu____5951 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5951] in
                          uu____5947 :: uu____5948 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5945 uu____5946 in
                      uu____5944 FStar_Pervasives_Native.None
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
        let flags1 =
          let uu____5966 =
            ((let uu____5969 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5969) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5971 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5971) in
          if uu____5966
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5980 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5984 =
            ((let uu____5987 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5987) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5984
          then c
          else
            (let uu____5991 = FStar_Syntax_Util.is_partial_return c in
             if uu____5991
             then c
             else
               (let uu____5995 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5995
                then
                  let uu____5998 =
                    let uu____5999 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5999 in
                  (if uu____5998
                   then
                     let uu____6002 =
                       let uu____6003 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____6004 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____6003 uu____6004 in
                     failwith uu____6002
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____6009 =
                        let uu____6010 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____6010 in
                      if uu____6009
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___312_6015 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___312_6015.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___312_6015.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___312_6015.FStar_Syntax_Syntax.effect_args);
                            FStar_Syntax_Syntax.flags = flags1
                          } in
                        FStar_Syntax_Syntax.mk_Comp retc2
                      else FStar_Syntax_Util.comp_set_flags retc flags1))
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
                     let uu____6026 =
                       let uu____6029 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____6029
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____6026 in
                   let eq1 =
                     let uu____6033 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____6033 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____6035 =
                     let uu____6036 =
                       let uu____6041 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____6041.FStar_Syntax_Syntax.comp in
                     uu____6036 () in
                   FStar_Syntax_Util.comp_set_flags uu____6035 flags1))) in
        let uu____6044 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____6044
        then lc
        else
          (let uu___313_6046 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___313_6046.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___313_6046.FStar_Syntax_Syntax.res_typ);
             FStar_Syntax_Syntax.cflags = flags1;
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
          let uu____6071 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____6071 with
          | FStar_Pervasives_Native.None  ->
              let uu____6080 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c' in
              let uu____6085 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____6080 uu____6085
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
            let uu____6118 =
              let uu____6119 = FStar_Syntax_Subst.compress t2 in
              uu____6119.FStar_Syntax_Syntax.n in
            match uu____6118 with
            | FStar_Syntax_Syntax.Tm_type uu____6122 -> true
            | uu____6123 -> false in
          let uu____6124 =
            let uu____6125 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____6125.FStar_Syntax_Syntax.n in
          match uu____6124 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6133 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____6144 =
                  let uu____6145 =
                    let uu____6146 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6146 in
                  (FStar_Pervasives_Native.None, uu____6145) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6144 in
              let e1 =
                let uu____6156 =
                  let uu____6157 =
                    let uu____6158 = FStar_Syntax_Syntax.as_arg e in
                    [uu____6158] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6157 in
                uu____6156 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____6163 -> (e, lc)
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
              (let uu____6192 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____6192 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6215 -> false) in
          let gopt =
            if use_eq
            then
              let uu____6237 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____6237, false)
            else
              (let uu____6243 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____6243, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6254) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6263 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ in
                FStar_Errors.raise_error uu____6263 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___314_6277 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___314_6277.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___314_6277.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___314_6277.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6282 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6282 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___315_6290 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___315_6290.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___315_6290.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___315_6290.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___316_6293 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___316_6293.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___316_6293.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___316_6293.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6299 =
                     let uu____6300 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6300
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6305 =
                          let uu____6306 = FStar_Syntax_Subst.compress f1 in
                          uu____6306.FStar_Syntax_Syntax.n in
                        match uu____6305 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6311,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6313;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6314;_},uu____6315)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___317_6337 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___317_6337.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___317_6337.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___317_6337.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6338 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6343 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6343
                              then
                                let uu____6344 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6345 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6346 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6347 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6344 uu____6345 uu____6346 uu____6347
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6350 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6350 with
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
                                  let uu____6363 = destruct_comp ct in
                                  (match uu____6363 with
                                   | (u_t,uu____6373,uu____6374) ->
                                       let wp =
                                         let uu____6378 =
                                           let uu____6379 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6380 =
                                             let uu____6381 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6382 =
                                               let uu____6385 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6385] in
                                             uu____6381 :: uu____6382 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6379 uu____6380 in
                                         uu____6378
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6389 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6389 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6399 =
                                             let uu____6400 =
                                               let uu____6401 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6401] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6400 in
                                           uu____6399
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6405 =
                                         let uu____6410 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6423 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6424 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6410
                                           uu____6423 e cret uu____6424 in
                                       (match uu____6405 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___318_6430 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___318_6430.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___318_6430.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6432 =
                                                let uu____6433 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6433 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6432
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6444 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6444
                                              then
                                                let uu____6445 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6445
                                              else ());
                                             c2)))))) in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___279_6455  ->
                             match uu___279_6455 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6458 -> [])) in
                   let lc1 =
                     let uu___319_6460 = lc in
                     let uu____6461 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6461;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags1;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___320_6463 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___320_6463.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___320_6463.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___320_6463.FStar_TypeChecker_Env.implicits)
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
        let uu____6486 =
          let uu____6487 =
            let uu____6488 =
              let uu____6489 =
                let uu____6490 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6490 in
              [uu____6489] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6488 in
          uu____6487 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6486 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6497 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6497
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6515 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6530 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6559)::(ens,uu____6561)::uu____6562 ->
                    let uu____6591 =
                      let uu____6594 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6594 in
                    let uu____6595 =
                      let uu____6596 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6596 in
                    (uu____6591, uu____6595)
                | uu____6599 ->
                    let uu____6608 =
                      let uu____6613 =
                        let uu____6614 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6614 in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6613) in
                    FStar_Errors.raise_error uu____6608
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6630)::uu____6631 ->
                    let uu____6650 =
                      let uu____6655 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6655 in
                    (match uu____6650 with
                     | (us_r,uu____6687) ->
                         let uu____6688 =
                           let uu____6693 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6693 in
                         (match uu____6688 with
                          | (us_e,uu____6725) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6728 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6728
                                  us_r in
                              let as_ens =
                                let uu____6730 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6730
                                  us_e in
                              let req =
                                let uu____6734 =
                                  let uu____6735 =
                                    let uu____6736 =
                                      let uu____6747 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6747] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6736 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6735 in
                                uu____6734 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6765 =
                                  let uu____6766 =
                                    let uu____6767 =
                                      let uu____6778 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6778] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6767 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6766 in
                                uu____6765 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6793 =
                                let uu____6796 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6796 in
                              let uu____6797 =
                                let uu____6798 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6798 in
                              (uu____6793, uu____6797)))
                | uu____6801 -> failwith "Impossible"))
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
      (let uu____6827 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6827
       then
         let uu____6828 = FStar_Syntax_Print.term_to_string tm in
         let uu____6829 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6828 uu____6829
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
        (let uu____6847 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6847
         then
           let uu____6848 = FStar_Syntax_Print.term_to_string tm in
           let uu____6849 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6848
             uu____6849
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6854 =
      let uu____6855 =
        let uu____6856 = FStar_Syntax_Subst.compress t in
        uu____6856.FStar_Syntax_Syntax.n in
      match uu____6855 with
      | FStar_Syntax_Syntax.Tm_app uu____6859 -> false
      | uu____6874 -> true in
    if uu____6854
    then t
    else
      (let uu____6876 = FStar_Syntax_Util.head_and_args t in
       match uu____6876 with
       | (head1,args) ->
           let uu____6913 =
             let uu____6914 =
               let uu____6915 = FStar_Syntax_Subst.compress head1 in
               uu____6915.FStar_Syntax_Syntax.n in
             match uu____6914 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6918 -> false in
           if uu____6913
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6940 ->
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
             let uu____6977 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6977 with
             | (formals,uu____6991) ->
                 let n_implicits =
                   let uu____7009 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7085  ->
                             match uu____7085 with
                             | (uu____7092,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____7009 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____7223 = FStar_TypeChecker_Env.expected_typ env in
             match uu____7223 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____7247 =
                     let uu____7252 =
                       let uu____7253 = FStar_Util.string_of_int n_expected in
                       let uu____7260 = FStar_Syntax_Print.term_to_string e in
                       let uu____7261 = FStar_Util.string_of_int n_available in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7253 uu____7260 uu____7261 in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7252) in
                   let uu____7268 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error uu____7247 uu____7268
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___280_7289 =
             match uu___280_7289 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7319 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7319 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7428) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7471,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7504 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7504 with
                           | (v1,uu____7544,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7561 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7561 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7654 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7654)))
                      | (uu____7681,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7727 =
                      let uu____7754 = inst_n_binders t in
                      aux [] uu____7754 bs1 in
                    (match uu____7727 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7825) -> (e, torig, guard)
                          | (uu____7856,[]) when
                              let uu____7887 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7887 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7888 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7920 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7935 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7943 =
      let uu____7946 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7946
        (FStar_List.map
           (fun u  ->
              let uu____7956 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7956 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7943 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7973 = FStar_Util.set_is_empty x in
      if uu____7973
      then []
      else
        (let s =
           let uu____7980 =
             let uu____7983 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7983 in
           FStar_All.pipe_right uu____7980 FStar_Util.set_elements in
         (let uu____7991 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7991
          then
            let uu____7992 =
              let uu____7993 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7993 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7992
          else ());
         (let r =
            let uu____8000 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____8000 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____8015 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____8015
                     then
                       let uu____8016 =
                         let uu____8017 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8017 in
                       let uu____8018 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____8019 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8016 uu____8018 uu____8019
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
        let uu____8041 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____8041 FStar_Util.fifo_set_elements in
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
        | ([],uu____8073) -> generalized_univ_names
        | (uu____8080,[]) -> explicit_univ_names
        | uu____8087 ->
            let uu____8096 =
              let uu____8101 =
                let uu____8102 = FStar_Syntax_Print.term_to_string t in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8102 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8101) in
            FStar_Errors.raise_error uu____8096 t.FStar_Syntax_Syntax.pos
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
      (let uu____8119 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____8119
       then
         let uu____8120 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____8120
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____8126 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____8126
        then
          let uu____8127 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____8127
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
        let uu____8197 =
          let uu____8198 =
            FStar_Util.for_all
              (fun uu____8211  ->
                 match uu____8211 with
                 | (uu____8220,uu____8221,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____8198 in
        if uu____8197
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8267 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8267
              then
                let uu____8268 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8268
              else ());
             (let c1 =
                let uu____8271 = FStar_TypeChecker_Env.should_verify env in
                if uu____8271
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
              (let uu____8274 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8274
               then
                 let uu____8275 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8275
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8336 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8336 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8466 =
             match uu____8466 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8532 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8532
                   then
                     let uu____8533 =
                       let uu____8534 =
                         let uu____8537 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8537
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8534
                         (FStar_String.concat ", ") in
                     let uu____8564 =
                       let uu____8565 =
                         let uu____8568 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8568
                           (FStar_List.map
                              (fun uu____8596  ->
                                 match uu____8596 with
                                 | (u,t2) ->
                                     let uu____8603 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8604 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8603 uu____8604)) in
                       FStar_All.pipe_right uu____8565
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8533
                       uu____8564
                   else ());
                  (let univs2 =
                     let uu____8611 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8634  ->
                            match uu____8634 with
                            | (uu____8643,t2) ->
                                let uu____8645 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8645)
                       univs1 uu____8611 in
                   let uvs = gen_uvars uvt in
                   (let uu____8668 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8668
                    then
                      let uu____8669 =
                        let uu____8670 =
                          let uu____8673 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8673
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8670
                          (FStar_String.concat ", ") in
                      let uu____8700 =
                        let uu____8701 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8733  ->
                                  match uu____8733 with
                                  | (u,t2) ->
                                      let uu____8740 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8741 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8740 uu____8741)) in
                        FStar_All.pipe_right uu____8701
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8669
                        uu____8700
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8771 =
             let uu____8804 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8804 in
           match uu____8771 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8922 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8922
                 then ()
                 else
                   (let uu____8924 = lec_hd in
                    match uu____8924 with
                    | (lb1,uu____8932,uu____8933) ->
                        let uu____8934 = lec2 in
                        (match uu____8934 with
                         | (lb2,uu____8942,uu____8943) ->
                             let msg =
                               let uu____8945 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8946 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8945 uu____8946 in
                             let uu____8947 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8947)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9058  ->
                           match uu____9058 with
                           | (u,uu____9066) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9088  ->
                                       match uu____9088 with
                                       | (u',uu____9096) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____9101 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____9101
                 then ()
                 else
                   (let uu____9103 = lec_hd in
                    match uu____9103 with
                    | (lb1,uu____9111,uu____9112) ->
                        let uu____9113 = lec2 in
                        (match uu____9113 with
                         | (lb2,uu____9121,uu____9122) ->
                             let msg =
                               let uu____9124 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____9125 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9124 uu____9125 in
                             let uu____9126 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9126)) in
               let lecs1 =
                 let uu____9136 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9195 = univs_and_uvars_of_lec this_lec in
                        match uu____9195 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9136 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9348 = lec_hd in
                   match uu____9348 with
                   | (lbname,e,c) ->
                       let uu____9358 =
                         let uu____9363 =
                           let uu____9364 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____9365 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____9366 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9364 uu____9365 uu____9366 in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9363) in
                       let uu____9367 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____9358 uu____9367 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9397  ->
                         match uu____9397 with
                         | (u,k) ->
                             let uu____9410 = FStar_Syntax_Unionfind.find u in
                             (match uu____9410 with
                              | FStar_Pervasives_Native.Some uu____9419 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9426 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9430 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9430 with
                                   | (bs,kres) ->
                                       ((let uu____9468 =
                                           let uu____9469 =
                                             let uu____9472 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9472 in
                                           uu____9469.FStar_Syntax_Syntax.n in
                                         match uu____9468 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9473 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9477 =
                                               let uu____9478 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9478 in
                                             if uu____9477
                                             then fail kres
                                             else ()
                                         | uu____9480 -> fail kres);
                                        (let a =
                                           let uu____9482 =
                                             let uu____9485 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9485 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9482 kres in
                                         let t =
                                           let uu____9489 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9489
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
                      (fun uu____9608  ->
                         match uu____9608 with
                         | (lbname,e,c) ->
                             let uu____9654 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9723 ->
                                   let uu____9738 = (e, c) in
                                   (match uu____9738 with
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
                                                (fun uu____9775  ->
                                                   match uu____9775 with
                                                   | (x,uu____9783) ->
                                                       let uu____9788 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9788)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9798 =
                                                let uu____9799 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9799 in
                                              if uu____9798
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
                                          let uu____9807 =
                                            let uu____9808 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9808.FStar_Syntax_Syntax.n in
                                          match uu____9807 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9831 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9831 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9846 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9848 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9848, gen_tvars)) in
                             (match uu____9654 with
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
        (let uu____9994 = Obj.magic () in ());
        (let uu____9996 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9996
         then
           let uu____9997 =
             let uu____9998 =
               FStar_List.map
                 (fun uu____10011  ->
                    match uu____10011 with
                    | (lb,uu____10019,uu____10020) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9998 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9997
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10041  ->
                match uu____10041 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____10070 = gen env is_rec lecs in
           match uu____10070 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10169  ->
                       match uu____10169 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10231 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10231
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10275  ->
                           match uu____10275 with
                           | (l,us,e,c,gvs) ->
                               let uu____10309 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10310 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10311 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10312 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10313 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10309 uu____10310 uu____10311
                                 uu____10312 uu____10313))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10354  ->
                match uu____10354 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10398 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10398, t, c, gvs)) univnames_lecs
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
              (let uu____10441 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21 in
               match uu____10441 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10447 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10447) in
          let is_var e1 =
            let uu____10454 =
              let uu____10455 = FStar_Syntax_Subst.compress e1 in
              uu____10455.FStar_Syntax_Syntax.n in
            match uu____10454 with
            | FStar_Syntax_Syntax.Tm_name uu____10458 -> true
            | uu____10459 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___321_10475 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___321_10475.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___321_10475.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10476 -> e2 in
          let env2 =
            let uu___322_10478 = env1 in
            let uu____10479 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___322_10478.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___322_10478.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___322_10478.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___322_10478.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___322_10478.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___322_10478.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___322_10478.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___322_10478.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___322_10478.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___322_10478.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___322_10478.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___322_10478.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___322_10478.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___322_10478.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___322_10478.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10479;
              FStar_TypeChecker_Env.is_iface =
                (uu___322_10478.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___322_10478.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___322_10478.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___322_10478.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___322_10478.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___322_10478.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___322_10478.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___322_10478.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___322_10478.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___322_10478.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___322_10478.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___322_10478.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___322_10478.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___322_10478.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___322_10478.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___322_10478.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___322_10478.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___322_10478.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10480 = check env2 t1 t2 in
          match uu____10480 with
          | FStar_Pervasives_Native.None  ->
              let uu____10487 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____10492 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____10487 uu____10492
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10499 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10499
                then
                  let uu____10500 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10500
                else ());
               (let uu____10502 = decorate e t2 in (uu____10502, g)))
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
        let uu____10530 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10530
        then
          let uu____10535 = discharge g1 in
          let uu____10536 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10535, uu____10536)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10549 =
               let uu____10550 =
                 let uu____10551 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10551 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10550
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10549
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10553 = destruct_comp c1 in
           match uu____10553 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10570 = FStar_TypeChecker_Env.get_range env in
                 let uu____10571 =
                   let uu____10572 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10573 =
                     let uu____10574 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10575 =
                       let uu____10578 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10578] in
                     uu____10574 :: uu____10575 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10572 uu____10573 in
                 uu____10571 FStar_Pervasives_Native.None uu____10570 in
               ((let uu____10582 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10582
                 then
                   let uu____10583 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10583
                 else ());
                (let g2 =
                   let uu____10586 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10586 in
                 let uu____10587 = discharge g2 in
                 let uu____10588 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10587, uu____10588))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___281_10612 =
        match uu___281_10612 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10620)::[] -> f fst1
        | uu____10637 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10642 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10642
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10651 =
          let uu____10654 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10654 in
        FStar_All.pipe_right uu____10651
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10665 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10665
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___282_10679 =
        match uu___282_10679 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10687)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10706)::[] ->
            let uu____10735 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10735
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10740 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10750 =
          let uu____10757 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10757) in
        let uu____10762 =
          let uu____10771 =
            let uu____10778 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10778) in
          let uu____10783 =
            let uu____10792 =
              let uu____10799 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10799) in
            let uu____10804 =
              let uu____10813 =
                let uu____10820 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10820) in
              let uu____10825 =
                let uu____10834 =
                  let uu____10841 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10841) in
                [uu____10834; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10813 :: uu____10825 in
            uu____10792 :: uu____10804 in
          uu____10771 :: uu____10783 in
        uu____10750 :: uu____10762 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10892 =
            FStar_Util.find_map table
              (fun uu____10905  ->
                 match uu____10905 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10922 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10922
                     else FStar_Pervasives_Native.None) in
          (match uu____10892 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10925 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10929 =
      let uu____10930 = FStar_Syntax_Util.un_uinst l in
      uu____10930.FStar_Syntax_Syntax.n in
    match uu____10929 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10934 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10958)::uu____10959 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10970 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10977,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10978))::uu____10979 -> bs
      | uu____10996 ->
          let uu____10997 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10997 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11001 =
                 let uu____11002 = FStar_Syntax_Subst.compress t in
                 uu____11002.FStar_Syntax_Syntax.n in
               (match uu____11001 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11006) ->
                    let uu____11023 =
                      FStar_Util.prefix_until
                        (fun uu___283_11063  ->
                           match uu___283_11063 with
                           | (uu____11070,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11071)) ->
                               false
                           | uu____11074 -> true) bs' in
                    (match uu____11023 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11109,uu____11110) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11182,uu____11183) ->
                         let uu____11256 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11274  ->
                                   match uu____11274 with
                                   | (x,uu____11282) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11256
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11329  ->
                                     match uu____11329 with
                                     | (x,i) ->
                                         let uu____11348 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11348, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11358 -> bs))
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
          let uu____11390 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11390
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
        (let uu____11413 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11413
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11415 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11415))
         else ());
        (let fv =
           let uu____11418 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11418
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
         let uu____11426 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___323_11432 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___323_11432.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___323_11432.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___323_11432.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___323_11432.FStar_Syntax_Syntax.sigattrs)
           }), uu____11426))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___284_11442 =
        match uu___284_11442 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11443 -> false in
      let reducibility uu___285_11447 =
        match uu___285_11447 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11448 -> false in
      let assumption uu___286_11452 =
        match uu___286_11452 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11453 -> false in
      let reification uu___287_11457 =
        match uu___287_11457 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11458 -> true
        | uu____11459 -> false in
      let inferred uu___288_11463 =
        match uu___288_11463 with
        | FStar_Syntax_Syntax.Discriminator uu____11464 -> true
        | FStar_Syntax_Syntax.Projector uu____11465 -> true
        | FStar_Syntax_Syntax.RecordType uu____11470 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11479 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11488 -> false in
      let has_eq uu___289_11492 =
        match uu___289_11492 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11493 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11553 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11558 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11562 =
        let uu____11563 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___290_11567  ->
                  match uu___290_11567 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11568 -> false)) in
        FStar_All.pipe_right uu____11563 Prims.op_Negation in
      if uu____11562
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11581 =
            let uu____11586 =
              let uu____11587 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11587 msg in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11586) in
          FStar_Errors.raise_error uu____11581 r in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11595 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11599 =
            let uu____11600 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11600 in
          if uu____11599 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11605),uu____11606) ->
              ((let uu____11622 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11622
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11626 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11626
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11632 ->
              let uu____11641 =
                let uu____11642 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11642 in
              if uu____11641 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11648 ->
              let uu____11655 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11655 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11659 ->
              let uu____11666 =
                let uu____11667 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11667 in
              if uu____11666 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11673 ->
              let uu____11674 =
                let uu____11675 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11675 in
              if uu____11674 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11681 ->
              let uu____11682 =
                let uu____11683 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11683 in
              if uu____11682 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11689 ->
              let uu____11702 =
                let uu____11703 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11703 in
              if uu____11702 then err'1 () else ()
          | uu____11709 -> ()))
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
                          let uu____11772 =
                            let uu____11775 =
                              let uu____11776 =
                                let uu____11783 =
                                  let uu____11784 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11784 in
                                (uu____11783, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11776 in
                            FStar_Syntax_Syntax.mk uu____11775 in
                          uu____11772 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11825  ->
                                  match uu____11825 with
                                  | (x,imp) ->
                                      let uu____11836 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11836, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11838 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11838 in
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
                             let uu____11847 =
                               let uu____11848 =
                                 let uu____11849 =
                                   let uu____11850 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11851 =
                                     let uu____11852 =
                                       let uu____11853 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11853 in
                                     [uu____11852] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11850
                                     uu____11851 in
                                 uu____11849 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11848 in
                             FStar_Syntax_Util.refine x uu____11847 in
                           let uu____11856 =
                             let uu___324_11857 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___324_11857.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___324_11857.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11856) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11872 =
                          FStar_List.map
                            (fun uu____11894  ->
                               match uu____11894 with
                               | (x,uu____11906) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11872 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11955  ->
                                match uu____11955 with
                                | (x,uu____11967) ->
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
                             (let uu____11981 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11981)
                               ||
                               (let uu____11983 =
                                  let uu____11984 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11984.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11983) in
                           let quals =
                             let uu____11988 =
                               let uu____11991 =
                                 let uu____11994 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11994
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11998 =
                                 FStar_List.filter
                                   (fun uu___291_12002  ->
                                      match uu___291_12002 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12003 -> false) iquals in
                               FStar_List.append uu____11991 uu____11998 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11988 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____12024 =
                                 let uu____12025 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12025 in
                               FStar_Syntax_Syntax.mk_Total uu____12024 in
                             let uu____12026 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12026 in
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
                           (let uu____12029 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____12029
                            then
                              let uu____12030 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12030
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
                                             fun uu____12083  ->
                                               match uu____12083 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12107 =
                                                       let uu____12110 =
                                                         let uu____12111 =
                                                           let uu____12118 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____12118,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12111 in
                                                       pos uu____12110 in
                                                     (uu____12107, b)
                                                   else
                                                     (let uu____12122 =
                                                        let uu____12125 =
                                                          let uu____12126 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12126 in
                                                        pos uu____12125 in
                                                      (uu____12122, b)))) in
                                   let pat_true =
                                     let uu____12144 =
                                       let uu____12147 =
                                         let uu____12148 =
                                           let uu____12161 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____12161, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12148 in
                                       pos uu____12147 in
                                     (uu____12144,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12195 =
                                       let uu____12198 =
                                         let uu____12199 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12199 in
                                       pos uu____12198 in
                                     (uu____12195,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12211 =
                                     let uu____12214 =
                                       let uu____12215 =
                                         let uu____12238 =
                                           let uu____12241 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12242 =
                                             let uu____12245 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12245] in
                                           uu____12241 :: uu____12242 in
                                         (arg_exp, uu____12238) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12215 in
                                     FStar_Syntax_Syntax.mk uu____12214 in
                                   uu____12211 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12252 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12252
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
                                let uu____12260 =
                                  let uu____12265 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12265 in
                                let uu____12266 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12260;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12266
                                } in
                              let impl =
                                let uu____12270 =
                                  let uu____12271 =
                                    let uu____12278 =
                                      let uu____12281 =
                                        let uu____12282 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12282
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12281] in
                                    ((false, [lb]), uu____12278) in
                                  FStar_Syntax_Syntax.Sig_let uu____12271 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12270;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12300 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12300
                               then
                                 let uu____12301 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12301
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
                                fun uu____12343  ->
                                  match uu____12343 with
                                  | (a,uu____12349) ->
                                      let uu____12350 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12350 with
                                       | (field_name,uu____12356) ->
                                           let field_proj_tm =
                                             let uu____12358 =
                                               let uu____12359 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12359 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12358 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12376 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12408  ->
                                    match uu____12408 with
                                    | (x,uu____12416) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12418 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12418 with
                                         | (field_name,uu____12426) ->
                                             let t =
                                               let uu____12428 =
                                                 let uu____12429 =
                                                   let uu____12432 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12432 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12429 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12428 in
                                             let only_decl =
                                               (let uu____12436 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12436)
                                                 ||
                                                 (let uu____12438 =
                                                    let uu____12439 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12439.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12438) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12453 =
                                                   FStar_List.filter
                                                     (fun uu___292_12457  ->
                                                        match uu___292_12457
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12458 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12453
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___293_12471  ->
                                                         match uu___293_12471
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12472 ->
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
                                             ((let uu____12491 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12491
                                               then
                                                 let uu____12492 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12492
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
                                                           fun uu____12540 
                                                             ->
                                                             match uu____12540
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12564
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12564,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12580
                                                                    =
                                                                    let uu____12583
                                                                    =
                                                                    let uu____12584
                                                                    =
                                                                    let uu____12591
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12591,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12584 in
                                                                    pos
                                                                    uu____12583 in
                                                                    (uu____12580,
                                                                    b))
                                                                   else
                                                                    (let uu____12595
                                                                    =
                                                                    let uu____12598
                                                                    =
                                                                    let uu____12599
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12599 in
                                                                    pos
                                                                    uu____12598 in
                                                                    (uu____12595,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12615 =
                                                     let uu____12618 =
                                                       let uu____12619 =
                                                         let uu____12632 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12632,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12619 in
                                                     pos uu____12618 in
                                                   let uu____12641 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12615,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12641) in
                                                 let body =
                                                   let uu____12653 =
                                                     let uu____12656 =
                                                       let uu____12657 =
                                                         let uu____12680 =
                                                           let uu____12683 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12683] in
                                                         (arg_exp,
                                                           uu____12680) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12657 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12656 in
                                                   uu____12653
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12691 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12691
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
                                                   let uu____12698 =
                                                     let uu____12703 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12703 in
                                                   let uu____12704 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12698;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12704
                                                   } in
                                                 let impl =
                                                   let uu____12708 =
                                                     let uu____12709 =
                                                       let uu____12716 =
                                                         let uu____12719 =
                                                           let uu____12720 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12720
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12719] in
                                                       ((false, [lb]),
                                                         uu____12716) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12709 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12708;
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
                                                 (let uu____12738 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12738
                                                  then
                                                    let uu____12739 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12739
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12376 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12779) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12784 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12784 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12806 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12806 with
                    | (formals,uu____12822) ->
                        let uu____12839 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12871 =
                                   let uu____12872 =
                                     let uu____12873 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12873 in
                                   FStar_Ident.lid_equals typ_lid uu____12872 in
                                 if uu____12871
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12892,uvs',tps,typ0,uu____12896,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12915 -> failwith "Impossible"
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
                        (match uu____12839 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12988 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12988 with
                              | (indices,uu____13004) ->
                                  let refine_domain =
                                    let uu____13022 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___294_13027  ->
                                              match uu___294_13027 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13028 -> true
                                              | uu____13037 -> false)) in
                                    if uu____13022
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___295_13045 =
                                      match uu___295_13045 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13048,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13060 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____13061 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____13061 with
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
                                    let uu____13072 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____13072 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13137  ->
                                               fun uu____13138  ->
                                                 match (uu____13137,
                                                         uu____13138)
                                                 with
                                                 | ((x,uu____13156),(x',uu____13158))
                                                     ->
                                                     let uu____13167 =
                                                       let uu____13174 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13174) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13167) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13175 -> []