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
      FStar_Errors.maybe_fatal_error uu____17 uu____18
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
  fun uu___328_93  ->
    match uu___328_93 with
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
                     let uu___347_257 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u in
                         (reason, env, uu____286, t, k, r) in
                       [uu____273] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___347_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___347_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___347_257.FStar_TypeChecker_Env.univ_ineqs);
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
            (FStar_Errors.UncontrainedUnificationVar, uu____397) in
          FStar_Errors.maybe_fatal_error r uu____392);
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
                            ((let uu___348_497 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___348_497.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___348_497.FStar_Syntax_Syntax.index);
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
                                (FStar_Errors.UnexpectedComputationTypeForLetRec,
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
              let uu____1073 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
              match uu____1073 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1074;
                  FStar_Syntax_Syntax.vars = uu____1075;_} ->
                  let uu____1078 = FStar_Syntax_Util.type_u () in
                  (match uu____1078 with | (t,uu____1084) -> new_uvar env1 t)
              | t -> tc_annot env1 t in
            let uu___349_1086 = x in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___349_1086.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___349_1086.FStar_Syntax_Syntax.index);
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
                  | uu____1151 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1159) ->
                let uu____1164 = FStar_Syntax_Util.type_u () in
                (match uu____1164 with
                 | (k,uu____1188) ->
                     let t = new_uvar env1 k in
                     let x1 =
                       let uu___350_1191 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___350_1191.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___350_1191.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       } in
                     let uu____1192 =
                       let uu____1197 =
                         FStar_TypeChecker_Env.all_binders env1 in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1197 t in
                     (match uu____1192 with
                      | (e,u) ->
                          let p2 =
                            let uu___351_1221 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___351_1221.FStar_Syntax_Syntax.p)
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
                let uu____1277 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1404  ->
                          fun uu____1405  ->
                            match (uu____1404, uu____1405) with
                            | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                                let uu____1594 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2 in
                                (match uu____1594 with
                                 | (b',a',w',env3,te,pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), ((pat, imp) :: pats1))))
                       ([], [], [], env1, [], [])) in
                (match uu____1277 with
                 | (b,a,w,env2,args,pats1) ->
                     let e =
                       let uu____1792 =
                         let uu____1795 =
                           let uu____1796 =
                             let uu____1803 =
                               let uu____1806 =
                                 let uu____1807 =
                                   FStar_Syntax_Syntax.fv_to_tm fv in
                                 let uu____1808 =
                                   FStar_All.pipe_right args FStar_List.rev in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1807
                                   uu____1808 in
                               uu____1806 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p in
                             (uu____1803,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app)) in
                           FStar_Syntax_Syntax.Tm_meta uu____1796 in
                         FStar_Syntax_Syntax.mk uu____1795 in
                       uu____1792 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     let uu____1820 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu____1831 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu____1842 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu____1820, uu____1831, uu____1842, env2, e,
                       (let uu___352_1864 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___352_1864.FStar_Syntax_Syntax.p)
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
                    (fun uu____1948  ->
                       match uu____1948 with
                       | (p2,imp) ->
                           let uu____1967 = elaborate_pat env1 p2 in
                           (uu____1967, imp)) pats in
                let uu____1972 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____1972 with
                 | (uu____1979,t) ->
                     let uu____1981 = FStar_Syntax_Util.arrow_formals t in
                     (match uu____1981 with
                      | (f,uu____1997) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2119::uu____2120) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.TooManyPatternArguments,
                                    "Too many pattern arguments")
                                  (FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | (uu____2171::uu____2172,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2250  ->
                                        match uu____2250 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2277 =
                                                     let uu____2280 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2280 in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2277
                                                     FStar_Syntax_Syntax.tun in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                 let uu____2282 =
                                                   maybe_dot inaccessible a r in
                                                 (uu____2282, true)
                                             | uu____2287 ->
                                                 let uu____2290 =
                                                   let uu____2295 =
                                                     let uu____2296 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2296 in
                                                   (FStar_Errors.InsufficientPatternArguments,
                                                     uu____2295) in
                                                 FStar_Errors.raise_error
                                                   uu____2290
                                                   (FStar_Ident.range_of_lid
                                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2370,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2371)) when p_imp ->
                                     let uu____2374 = aux formals' pats' in
                                     (p2, true) :: uu____2374
                                 | (uu____2391,FStar_Pervasives_Native.Some
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
                                     let uu____2399 = aux formals' pats2 in
                                     (p3, true) :: uu____2399
                                 | (uu____2416,imp) ->
                                     let uu____2422 =
                                       let uu____2429 =
                                         FStar_Syntax_Syntax.is_implicit imp in
                                       (p2, uu____2429) in
                                     let uu____2432 = aux formals' pats' in
                                     uu____2422 :: uu____2432) in
                          let uu___353_2447 = p1 in
                          let uu____2450 =
                            let uu____2451 =
                              let uu____2464 = aux f pats1 in
                              (fv, uu____2464) in
                            FStar_Syntax_Syntax.Pat_cons uu____2451 in
                          {
                            FStar_Syntax_Syntax.v = uu____2450;
                            FStar_Syntax_Syntax.p =
                              (uu___353_2447.FStar_Syntax_Syntax.p)
                          }))
            | uu____2481 -> p1 in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu____2515 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
            match uu____2515 with
            | (b,a,w,env2,arg,p3) ->
                let uu____2568 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu____2568 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2592 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                     FStar_Errors.raise_error uu____2592
                       p3.FStar_Syntax_Syntax.p
                 | uu____2613 -> (b, a, w, arg, p3)) in
          let uu____2622 = one_pat true env p in
          match uu____2622 with
          | (b,uu____2648,uu____2649,tm,p1) -> (b, tm, p1)
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
          | (uu____2694,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2696)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2701,uu____2702) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2706 =
                    let uu____2707 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2708 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2707 uu____2708 in
                  failwith uu____2706)
               else ();
               (let uu____2711 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2711
                then
                  let uu____2712 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2713 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2712
                    uu____2713
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___354_2717 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___354_2717.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___354_2717.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2721 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2721
                then
                  let uu____2722 =
                    let uu____2723 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2724 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2723 uu____2724 in
                  failwith uu____2722
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___355_2728 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___355_2728.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___355_2728.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2730),uu____2731) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2753 =
                  let uu____2754 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2754 in
                if uu____2753
                then
                  let uu____2755 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2755
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2774;
                FStar_Syntax_Syntax.vars = uu____2775;_},args))
              ->
              ((let uu____2814 =
                  let uu____2815 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2815 Prims.op_Negation in
                if uu____2814
                then
                  let uu____2816 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2816
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2952)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3027) ->
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
                       | ((e2,imp),uu____3064) ->
                           let pat =
                             let uu____3086 = aux argpat e2 in
                             let uu____3087 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3086, uu____3087) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3092 ->
                      let uu____3115 =
                        let uu____3116 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3117 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3116 uu____3117 in
                      failwith uu____3115 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3129;
                     FStar_Syntax_Syntax.vars = uu____3130;_},uu____3131);
                FStar_Syntax_Syntax.pos = uu____3132;
                FStar_Syntax_Syntax.vars = uu____3133;_},args))
              ->
              ((let uu____3176 =
                  let uu____3177 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3177 Prims.op_Negation in
                if uu____3176
                then
                  let uu____3178 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3178
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3314)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3389) ->
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
                       | ((e2,imp),uu____3426) ->
                           let pat =
                             let uu____3448 = aux argpat e2 in
                             let uu____3449 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3448, uu____3449) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3454 ->
                      let uu____3477 =
                        let uu____3478 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3479 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3478 uu____3479 in
                      failwith uu____3477 in
                match_args [] args argpats))
          | uu____3488 ->
              let uu____3493 =
                let uu____3494 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3495 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3496 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3494 uu____3495 uu____3496 in
              failwith uu____3493 in
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
    let pat_as_arg uu____3533 =
      match uu____3533 with
      | (p,i) ->
          let uu____3550 = decorated_pattern_as_term p in
          (match uu____3550 with
           | (vars,te) ->
               let uu____3573 =
                 let uu____3578 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3578) in
               (vars, uu____3573)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3592 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3592)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3596 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3596)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3600 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3600)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3621 =
          let uu____3636 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3636 FStar_List.unzip in
        (match uu____3621 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3746 =
               let uu____3747 =
                 let uu____3748 =
                   let uu____3763 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3763, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3748 in
               mk1 uu____3747 in
             (vars1, uu____3746))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3803)::[] -> wp
      | uu____3820 ->
          let uu____3829 =
            let uu____3830 =
              let uu____3831 =
                FStar_List.map
                  (fun uu____3841  ->
                     match uu____3841 with
                     | (x,uu____3847) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3831 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3830 in
          failwith uu____3829 in
    let uu____3852 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3852, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3866 = destruct_comp c in
        match uu____3866 with
        | (u,uu____3874,wp) ->
            let uu____3876 =
              let uu____3885 =
                let uu____3886 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____3886 in
              [uu____3885] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3876;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3896 =
          let uu____3903 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____3904 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____3903 uu____3904 in
        match uu____3896 with | (m,uu____3906,uu____3907) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3917 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____3917
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
        let uu____3954 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____3954 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____3991 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____3991 with
             | (a,kwp) ->
                 let uu____4022 = destruct_comp m1 in
                 let uu____4029 = destruct_comp m2 in
                 ((md, a, kwp), uu____4022, uu____4029))
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
            let uu____4091 =
              let uu____4092 =
                let uu____4101 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4101] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4092;
                FStar_Syntax_Syntax.flags = flags1
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4091
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
      let uu___356_4140 = lc in
      let uu____4141 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___356_4140.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4141;
        FStar_Syntax_Syntax.cflags =
          (uu___356_4140.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4146  ->
             let uu____4147 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4147)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4151 =
      let uu____4152 = FStar_Syntax_Subst.compress t in
      uu____4152.FStar_Syntax_Syntax.n in
    match uu____4151 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4155 -> true
    | uu____4168 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4182 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4182
        then c
        else
          (let uu____4184 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4184
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4223 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4223] in
                       let us =
                         let uu____4227 =
                           let uu____4230 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4230] in
                         u_res :: uu____4227 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4234 =
                         let uu____4235 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4236 =
                           let uu____4237 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4238 =
                             let uu____4241 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4242 =
                               let uu____4245 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4245] in
                             uu____4241 :: uu____4242 in
                           uu____4237 :: uu____4238 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4235 uu____4236 in
                       uu____4234 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4249 = destruct_comp c1 in
              match uu____4249 with
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
        let close1 uu____4277 =
          let uu____4278 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4278 in
        let uu___357_4279 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___357_4279.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___357_4279.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___357_4279.FStar_Syntax_Syntax.cflags);
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
          let uu____4290 =
            let uu____4291 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4291 in
          if uu____4290
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let uu____4293 = FStar_Syntax_Util.is_unit t in
             if uu____4293
             then
               FStar_Syntax_Syntax.mk_Total' t
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
             else
               (let m =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Parser_Const.effect_PURE_lid in
                let u_t = env.FStar_TypeChecker_Env.universe_of env t in
                let wp =
                  let uu____4298 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ()) in
                  if uu____4298
                  then FStar_Syntax_Syntax.tun
                  else
                    (let uu____4300 =
                       FStar_TypeChecker_Env.wp_signature env
                         FStar_Parser_Const.effect_PURE_lid in
                     match uu____4300 with
                     | (a,kwp) ->
                         let k =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (a, t)] kwp in
                         let uu____4308 =
                           let uu____4309 =
                             let uu____4310 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                             let uu____4311 =
                               let uu____4312 = FStar_Syntax_Syntax.as_arg t in
                               let uu____4313 =
                                 let uu____4316 =
                                   FStar_Syntax_Syntax.as_arg v1 in
                                 [uu____4316] in
                               uu____4312 :: uu____4313 in
                             FStar_Syntax_Syntax.mk_Tm_app uu____4310
                               uu____4311 in
                           uu____4309 FStar_Pervasives_Native.None
                             v1.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.NoFullNorm] env
                           uu____4308) in
                mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN])) in
        (let uu____4320 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4320
         then
           let uu____4321 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4322 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4323 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4321
             uu____4322 uu____4323
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
          fun uu____4341  ->
            match uu____4341 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4354 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4354
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4357 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4359 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4360 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4357 uu____4359 bstr uu____4360
                  else ());
                 (let bind_it uu____4365 =
                    let uu____4366 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4366
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4376 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4376
                        then
                          let uu____4377 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4379 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4380 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4381 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4382 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4377 uu____4379 uu____4380 uu____4381
                            uu____4382
                        else ());
                       (let try_simplify uu____4397 =
                          let aux uu____4411 =
                            let uu____4412 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4412
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4441 ->
                                  let uu____4442 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4442
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4469 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4469
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4525 =
                                  let uu____4530 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4530, reason) in
                                FStar_Util.Inl uu____4525
                            | uu____4535 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4554 =
                              let uu____4555 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4555.FStar_Syntax_Syntax.n in
                            match uu____4554 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4559) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4565 -> c in
                          let uu____4566 =
                            let uu____4567 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4567 in
                          if uu____4566
                          then
                            let uu____4580 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4580
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4600 =
                                  FStar_TypeChecker_Env.get_range env in
                                FStar_Errors.raise_error
                                  (FStar_Errors.NonTrivialPreConditionInPrims,
                                    "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                  uu____4600))
                          else
                            (let uu____4612 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4612
                             then subst_c2 "both total"
                             else
                               (let uu____4624 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4624
                                then
                                  let uu____4635 =
                                    let uu____4640 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4640, "both gtot") in
                                  FStar_Util.Inl uu____4635
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4666 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4668 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4668) in
                                       if uu____4666
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___358_4681 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___358_4681.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___358_4681.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4682 =
                                           let uu____4687 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4687, "c1 Tot") in
                                         FStar_Util.Inl uu____4682
                                       else aux ()
                                   | uu____4693 -> aux ()))) in
                        let uu____4702 = try_simplify () in
                        match uu____4702 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4726 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4726
                              then
                                let uu____4727 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4728 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4729 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4727 uu____4728 uu____4729
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4738 = lift_and_destruct env c1 c2 in
                            (match uu____4738 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4795 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4795]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4797 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4797] in
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
                                   let uu____4810 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4811 =
                                     let uu____4814 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4815 =
                                       let uu____4818 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4819 =
                                         let uu____4822 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4823 =
                                           let uu____4826 =
                                             let uu____4827 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4827 in
                                           [uu____4826] in
                                         uu____4822 :: uu____4823 in
                                       uu____4818 :: uu____4819 in
                                     uu____4814 :: uu____4815 in
                                   uu____4810 :: uu____4811 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4832 =
                                     let uu____4833 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4833
                                       wp_args in
                                   uu____4832 FStar_Pervasives_Native.None
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
              let uu____4873 =
                let uu____4874 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4874 in
              if uu____4873
              then f
              else (let uu____4876 = reason1 () in label uu____4876 r f)
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
            let uu___359_4887 = g in
            let uu____4888 =
              let uu____4889 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4889 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4888;
              FStar_TypeChecker_Env.deferred =
                (uu___359_4887.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___359_4887.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___359_4887.FStar_TypeChecker_Env.implicits)
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
      | uu____4899 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4918 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____4922 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____4922
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____4929 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____4929
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____4934 = destruct_comp c1 in
                    match uu____4934 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____4950 =
                            let uu____4951 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____4952 =
                              let uu____4953 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____4954 =
                                let uu____4957 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____4958 =
                                  let uu____4961 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____4961] in
                                uu____4957 :: uu____4958 in
                              uu____4953 :: uu____4954 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____4951
                              uu____4952 in
                          uu____4950 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___360_4964 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___360_4964.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___360_4964.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___360_4964.FStar_Syntax_Syntax.cflags);
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
            let uu____4997 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____4997
            then (lc, g0)
            else
              ((let uu____5004 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5004
                then
                  let uu____5005 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5006 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5005 uu____5006
                else ());
               (let flags1 =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___329_5016  ->
                          match uu___329_5016 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5019 -> [])) in
                let strengthen uu____5025 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5033 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5033 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5040 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5042 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5042) in
                           if uu____5040
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5049 =
                                 let uu____5050 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5050 in
                               FStar_Syntax_Util.comp_set_flags uu____5049
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5056 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5056
                           then
                             let uu____5057 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5058 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5057 uu____5058
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5061 = destruct_comp c2 in
                           match uu____5061 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5077 =
                                   let uu____5078 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5079 =
                                     let uu____5080 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5081 =
                                       let uu____5084 =
                                         let uu____5085 =
                                           let uu____5086 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5086 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5085 in
                                       let uu____5087 =
                                         let uu____5090 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5090] in
                                       uu____5084 :: uu____5087 in
                                     uu____5080 :: uu____5081 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5078
                                     uu____5079 in
                                 uu____5077 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5094 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5094
                                 then
                                   let uu____5095 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5095
                                 else ());
                                (let c21 =
                                   mk_comp md u_res_t res_t wp1 flags1 in
                                 c21))))) in
                let uu____5098 =
                  let uu___361_5099 = lc in
                  let uu____5100 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5101 =
                    let uu____5104 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5106 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5106) in
                    if uu____5104 then flags1 else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5100;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___361_5099.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5101;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5098,
                  (let uu___362_5111 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___362_5111.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___362_5111.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___362_5111.FStar_TypeChecker_Env.implicits)
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
        let uu____5126 =
          let uu____5131 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5132 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5131, uu____5132) in
        match uu____5126 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5141 =
                let uu____5142 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5143 =
                  let uu____5144 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5145 =
                    let uu____5148 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5148] in
                  uu____5144 :: uu____5145 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5142 uu____5143 in
              uu____5141 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5154 =
                let uu____5155 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5156 =
                  let uu____5157 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5158 =
                    let uu____5161 =
                      let uu____5162 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5162 in
                    let uu____5163 =
                      let uu____5166 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5166] in
                    uu____5161 :: uu____5163 in
                  uu____5157 :: uu____5158 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5155 uu____5156 in
              uu____5154 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5172 =
                let uu____5173 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5174 =
                  let uu____5175 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5176 =
                    let uu____5179 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5180 =
                      let uu____5183 =
                        let uu____5184 =
                          let uu____5185 =
                            let uu____5186 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5186] in
                          FStar_Syntax_Util.abs uu____5185 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5184 in
                      [uu____5183] in
                    uu____5179 :: uu____5180 in
                  uu____5175 :: uu____5176 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5173 uu____5174 in
              uu____5172 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5193 = FStar_TypeChecker_Env.get_range env in
              bind uu____5193 env FStar_Pervasives_Native.None
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
          let comp uu____5212 =
            let uu____5213 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5213
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5216 =
                 let uu____5241 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5242 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5241 uu____5242 in
               match uu____5216 with
               | ((md,uu____5244,uu____5245),(u_res_t,res_t,wp_then),
                  (uu____5249,uu____5250,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5288 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5289 =
                       let uu____5290 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5291 =
                         let uu____5292 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5293 =
                           let uu____5296 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5297 =
                             let uu____5300 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5301 =
                               let uu____5304 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5304] in
                             uu____5300 :: uu____5301 in
                           uu____5296 :: uu____5297 in
                         uu____5292 :: uu____5293 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5290 uu____5291 in
                     uu____5289 FStar_Pervasives_Native.None uu____5288 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5310 =
                     let uu____5311 = FStar_Options.split_cases () in
                     uu____5311 > (Prims.parse_int "0") in
                   if uu____5310
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5317 =
                          let uu____5318 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5319 =
                            let uu____5320 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5321 =
                              let uu____5324 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5324] in
                            uu____5320 :: uu____5321 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5318 uu____5319 in
                        uu____5317 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5327 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5327;
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
      let uu____5334 =
        let uu____5335 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5335 in
      FStar_Syntax_Syntax.fvar uu____5334 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5367  ->
                 match uu____5367 with
                 | (uu____5372,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5377 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5379 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5379
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5399 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5400 =
                 let uu____5401 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5402 =
                   let uu____5403 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5404 =
                     let uu____5407 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5408 =
                       let uu____5411 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5412 =
                         let uu____5415 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5415] in
                       uu____5411 :: uu____5412 in
                     uu____5407 :: uu____5408 in
                   uu____5403 :: uu____5404 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5401 uu____5402 in
               uu____5400 FStar_Pervasives_Native.None uu____5399 in
             let default_case =
               let post_k =
                 let uu____5422 =
                   let uu____5429 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5429] in
                 let uu____5430 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5422 uu____5430 in
               let kwp =
                 let uu____5436 =
                   let uu____5443 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5443] in
                 let uu____5444 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5436 uu____5444 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5449 =
                   let uu____5450 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5450] in
                 let uu____5451 =
                   let uu____5452 =
                     let uu____5455 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5455 in
                   let uu____5456 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5452 uu____5456 in
                 FStar_Syntax_Util.abs uu____5449 uu____5451
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
                 (fun uu____5480  ->
                    fun celse  ->
                      match uu____5480 with
                      | (g,cthen) ->
                          let uu____5488 =
                            let uu____5513 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5513 celse in
                          (match uu____5488 with
                           | ((md,uu____5515,uu____5516),(uu____5517,uu____5518,wp_then),
                              (uu____5520,uu____5521,wp_else)) ->
                               let uu____5541 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5541 []))
                 lcases default_case in
             let uu____5542 =
               let uu____5543 = FStar_Options.split_cases () in
               uu____5543 > (Prims.parse_int "0") in
             if uu____5542
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5547 = destruct_comp comp1 in
                match uu____5547 with
                | (uu____5554,uu____5555,wp) ->
                    let wp1 =
                      let uu____5560 =
                        let uu____5561 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5562 =
                          let uu____5563 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5564 =
                            let uu____5567 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5567] in
                          uu____5563 :: uu____5564 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5561 uu____5562 in
                      uu____5560 FStar_Pervasives_Native.None
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
          let uu____5582 =
            ((let uu____5585 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5585) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5587 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5587) in
          if uu____5582
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5596 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5600 =
            ((let uu____5603 =
                is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
              Prims.op_Negation uu____5603) ||
               (FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ))
              || env.FStar_TypeChecker_Env.lax in
          if uu____5600
          then c
          else
            (let uu____5607 = FStar_Syntax_Util.is_partial_return c in
             if uu____5607
             then c
             else
               (let uu____5611 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5611
                then
                  let uu____5614 =
                    let uu____5615 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5615 in
                  (if uu____5614
                   then
                     let uu____5618 =
                       let uu____5619 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5620 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5619 uu____5620 in
                     failwith uu____5618
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5625 =
                        let uu____5626 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5626 in
                      if uu____5625
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___363_5631 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___363_5631.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___363_5631.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___363_5631.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5642 =
                       let uu____5645 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5645
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5642 in
                   let eq1 =
                     let uu____5649 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5649 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5651 =
                     let uu____5652 =
                       let uu____5657 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5657.FStar_Syntax_Syntax.comp in
                     uu____5652 () in
                   FStar_Syntax_Util.comp_set_flags uu____5651 flags1))) in
        let uu____5660 =
          FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ in
        if uu____5660
        then lc
        else
          (let uu___364_5662 = lc in
           {
             FStar_Syntax_Syntax.eff_name =
               (uu___364_5662.FStar_Syntax_Syntax.eff_name);
             FStar_Syntax_Syntax.res_typ =
               (uu___364_5662.FStar_Syntax_Syntax.res_typ);
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
          let uu____5687 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5687 with
          | FStar_Pervasives_Native.None  ->
              let uu____5696 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c' in
              let uu____5701 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.raise_error uu____5696 uu____5701
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
            let uu____5734 =
              let uu____5735 = FStar_Syntax_Subst.compress t2 in
              uu____5735.FStar_Syntax_Syntax.n in
            match uu____5734 with
            | FStar_Syntax_Syntax.Tm_type uu____5738 -> true
            | uu____5739 -> false in
          let uu____5740 =
            let uu____5741 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5741.FStar_Syntax_Syntax.n in
          match uu____5740 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5749 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5760 =
                  let uu____5761 =
                    let uu____5762 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5762 in
                  (FStar_Pervasives_Native.None, uu____5761) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5760 in
              let e1 =
                let uu____5772 =
                  let uu____5773 =
                    let uu____5774 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5774] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5773 in
                uu____5772 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5779 -> (e, lc)
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
              (let uu____5808 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5808 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5831 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5853 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5853, false)
            else
              (let uu____5859 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5859, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____5870) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____5879 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ in
                FStar_Errors.raise_error uu____5879 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___365_5893 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___365_5893.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___365_5893.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___365_5893.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____5898 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____5898 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___366_5906 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___366_5906.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___366_5906.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___366_5906.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___367_5909 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___367_5909.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___367_5909.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___367_5909.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____5915 =
                     let uu____5916 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____5916
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____5921 =
                          let uu____5922 = FStar_Syntax_Subst.compress f1 in
                          uu____5922.FStar_Syntax_Syntax.n in
                        match uu____5921 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____5927,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____5929;
                                          FStar_Syntax_Syntax.vars =
                                            uu____5930;_},uu____5931)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___368_5953 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___368_5953.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___368_5953.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___368_5953.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____5954 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____5959 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____5959
                              then
                                let uu____5960 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____5961 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____5962 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____5963 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____5960 uu____5961 uu____5962 uu____5963
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____5966 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____5966 with
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
                                  let uu____5979 = destruct_comp ct in
                                  (match uu____5979 with
                                   | (u_t,uu____5989,uu____5990) ->
                                       let wp =
                                         let uu____5994 =
                                           let uu____5995 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____5996 =
                                             let uu____5997 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____5998 =
                                               let uu____6001 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6001] in
                                             uu____5997 :: uu____5998 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5995 uu____5996 in
                                         uu____5994
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6005 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6005 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6015 =
                                             let uu____6016 =
                                               let uu____6017 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6017] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6016 in
                                           uu____6015
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6021 =
                                         let uu____6026 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6039 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6040 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6026
                                           uu____6039 e cret uu____6040 in
                                       (match uu____6021 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___369_6046 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___369_6046.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___369_6046.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6048 =
                                                let uu____6049 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6049 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6048
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6060 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6060
                                              then
                                                let uu____6061 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6061
                                              else ());
                                             c2)))))) in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___330_6071  ->
                             match uu___330_6071 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6074 -> [])) in
                   let lc1 =
                     let uu___370_6076 = lc in
                     let uu____6077 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6077;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags1;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___371_6079 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___371_6079.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___371_6079.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___371_6079.FStar_TypeChecker_Env.implicits)
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
        let uu____6102 =
          let uu____6103 =
            let uu____6104 =
              let uu____6105 =
                let uu____6106 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6106 in
              [uu____6105] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6104 in
          uu____6103 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6102 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6113 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6113
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6131 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6146 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6175)::(ens,uu____6177)::uu____6178 ->
                    let uu____6207 =
                      let uu____6210 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6210 in
                    let uu____6211 =
                      let uu____6212 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6212 in
                    (uu____6207, uu____6211)
                | uu____6215 ->
                    let uu____6224 =
                      let uu____6229 =
                        let uu____6230 =
                          FStar_Syntax_Print.comp_to_string comp in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6230 in
                      (FStar_Errors.EffectConstructorNotFullyApplied,
                        uu____6229) in
                    FStar_Errors.raise_error uu____6224
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6246)::uu____6247 ->
                    let uu____6266 =
                      let uu____6271 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6271 in
                    (match uu____6266 with
                     | (us_r,uu____6303) ->
                         let uu____6304 =
                           let uu____6309 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6309 in
                         (match uu____6304 with
                          | (us_e,uu____6341) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6344 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6344
                                  us_r in
                              let as_ens =
                                let uu____6346 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6346
                                  us_e in
                              let req =
                                let uu____6350 =
                                  let uu____6351 =
                                    let uu____6352 =
                                      let uu____6363 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6363] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6352 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6351 in
                                uu____6350 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6381 =
                                  let uu____6382 =
                                    let uu____6383 =
                                      let uu____6394 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6394] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6383 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6382 in
                                uu____6381 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6409 =
                                let uu____6412 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6412 in
                              let uu____6413 =
                                let uu____6414 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6414 in
                              (uu____6409, uu____6413)))
                | uu____6417 -> failwith "Impossible"))
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
      (let uu____6443 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6443
       then
         let uu____6444 = FStar_Syntax_Print.term_to_string tm in
         let uu____6445 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6444 uu____6445
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
        (let uu____6463 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6463
         then
           let uu____6464 = FStar_Syntax_Print.term_to_string tm in
           let uu____6465 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6464
             uu____6465
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6470 =
      let uu____6471 =
        let uu____6472 = FStar_Syntax_Subst.compress t in
        uu____6472.FStar_Syntax_Syntax.n in
      match uu____6471 with
      | FStar_Syntax_Syntax.Tm_app uu____6475 -> false
      | uu____6490 -> true in
    if uu____6470
    then t
    else
      (let uu____6492 = FStar_Syntax_Util.head_and_args t in
       match uu____6492 with
       | (head1,args) ->
           let uu____6529 =
             let uu____6530 =
               let uu____6531 = FStar_Syntax_Subst.compress head1 in
               uu____6531.FStar_Syntax_Syntax.n in
             match uu____6530 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6534 -> false in
           if uu____6529
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6556 ->
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
             let uu____6593 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6593 with
             | (formals,uu____6607) ->
                 let n_implicits =
                   let uu____6625 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6701  ->
                             match uu____6701 with
                             | (uu____6708,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6625 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6839 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6839 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____6863 =
                     let uu____6868 =
                       let uu____6869 = FStar_Util.string_of_int n_expected in
                       let uu____6876 = FStar_Syntax_Print.term_to_string e in
                       let uu____6877 = FStar_Util.string_of_int n_available in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____6869 uu____6876 uu____6877 in
                     (FStar_Errors.MissingImplicitArguments, uu____6868) in
                   let uu____6884 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error uu____6863 uu____6884
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___331_6905 =
             match uu___331_6905 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____6935 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____6935 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7044) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7087,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7120 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7120 with
                           | (v1,uu____7160,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7177 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7177 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7270 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7270)))
                      | (uu____7297,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7343 =
                      let uu____7370 = inst_n_binders t in
                      aux [] uu____7370 bs1 in
                    (match uu____7343 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7441) -> (e, torig, guard)
                          | (uu____7472,[]) when
                              let uu____7503 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7503 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7504 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7536 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7551 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7559 =
      let uu____7562 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7562
        (FStar_List.map
           (fun u  ->
              let uu____7572 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7572 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7559 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7589 = FStar_Util.set_is_empty x in
      if uu____7589
      then []
      else
        (let s =
           let uu____7596 =
             let uu____7599 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7599 in
           FStar_All.pipe_right uu____7596 FStar_Util.set_elements in
         (let uu____7607 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7607
          then
            let uu____7608 =
              let uu____7609 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7609 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7608
          else ());
         (let r =
            let uu____7616 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7616 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7631 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7631
                     then
                       let uu____7632 =
                         let uu____7633 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7633 in
                       let uu____7634 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7635 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7632 uu____7634 uu____7635
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
        let uu____7657 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7657 FStar_Util.fifo_set_elements in
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
        | ([],uu____7689) -> generalized_univ_names
        | (uu____7696,[]) -> explicit_univ_names
        | uu____7703 ->
            let uu____7712 =
              let uu____7717 =
                let uu____7718 = FStar_Syntax_Print.term_to_string t in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7718 in
              (FStar_Errors.UnexpectedGeneralizedUniverse, uu____7717) in
            FStar_Errors.raise_error uu____7712 t.FStar_Syntax_Syntax.pos
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
      (let uu____7735 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7735
       then
         let uu____7736 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7736
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7742 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7742
        then
          let uu____7743 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7743
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
        let uu____7813 =
          let uu____7814 =
            FStar_Util.for_all
              (fun uu____7827  ->
                 match uu____7827 with
                 | (uu____7836,uu____7837,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7814 in
        if uu____7813
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7883 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____7883
              then
                let uu____7884 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7884
              else ());
             (let c1 =
                let uu____7887 = FStar_TypeChecker_Env.should_verify env in
                if uu____7887
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
              (let uu____7890 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____7890
               then
                 let uu____7891 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7891
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____7952 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____7952 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8082 =
             match uu____8082 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8148 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8148
                   then
                     let uu____8149 =
                       let uu____8150 =
                         let uu____8153 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8153
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8150
                         (FStar_String.concat ", ") in
                     let uu____8180 =
                       let uu____8181 =
                         let uu____8184 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8184
                           (FStar_List.map
                              (fun uu____8212  ->
                                 match uu____8212 with
                                 | (u,t2) ->
                                     let uu____8219 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8220 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8219 uu____8220)) in
                       FStar_All.pipe_right uu____8181
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8149
                       uu____8180
                   else ());
                  (let univs2 =
                     let uu____8227 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8250  ->
                            match uu____8250 with
                            | (uu____8259,t2) ->
                                let uu____8261 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8261)
                       univs1 uu____8227 in
                   let uvs = gen_uvars uvt in
                   (let uu____8284 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8284
                    then
                      let uu____8285 =
                        let uu____8286 =
                          let uu____8289 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8289
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8286
                          (FStar_String.concat ", ") in
                      let uu____8316 =
                        let uu____8317 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8349  ->
                                  match uu____8349 with
                                  | (u,t2) ->
                                      let uu____8356 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8357 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8356 uu____8357)) in
                        FStar_All.pipe_right uu____8317
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8285
                        uu____8316
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8387 =
             let uu____8420 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8420 in
           match uu____8387 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8538 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8538
                 then ()
                 else
                   (let uu____8540 = lec_hd in
                    match uu____8540 with
                    | (lb1,uu____8548,uu____8549) ->
                        let uu____8550 = lec2 in
                        (match uu____8550 with
                         | (lb2,uu____8558,uu____8559) ->
                             let msg =
                               let uu____8561 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8562 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8561 uu____8562 in
                             let uu____8563 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.IncompatibleSetOfUniverse, msg)
                               uu____8563)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8674  ->
                           match uu____8674 with
                           | (u,uu____8682) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8704  ->
                                       match uu____8704 with
                                       | (u',uu____8712) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8717 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8717
                 then ()
                 else
                   (let uu____8719 = lec_hd in
                    match uu____8719 with
                    | (lb1,uu____8727,uu____8728) ->
                        let uu____8729 = lec2 in
                        (match uu____8729 with
                         | (lb2,uu____8737,uu____8738) ->
                             let msg =
                               let uu____8740 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8741 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8740 uu____8741 in
                             let uu____8742 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_Errors.raise_error
                               (FStar_Errors.IncompatibleNumberOfTypes, msg)
                               uu____8742)) in
               let lecs1 =
                 let uu____8752 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8811 = univs_and_uvars_of_lec this_lec in
                        match uu____8811 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8752 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____8964 = lec_hd in
                   match uu____8964 with
                   | (lbname,e,c) ->
                       let uu____8974 =
                         let uu____8979 =
                           let uu____8980 =
                             FStar_Syntax_Print.term_to_string k in
                           let uu____8981 =
                             FStar_Syntax_Print.lbname_to_string lbname in
                           let uu____8982 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c) in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____8980 uu____8981 uu____8982 in
                         (FStar_Errors.FailToResolveImplicitArgument,
                           uu____8979) in
                       let uu____8983 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error uu____8974 uu____8983 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9013  ->
                         match uu____9013 with
                         | (u,k) ->
                             let uu____9026 = FStar_Syntax_Unionfind.find u in
                             (match uu____9026 with
                              | FStar_Pervasives_Native.Some uu____9035 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9042 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9046 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9046 with
                                   | (bs,kres) ->
                                       ((let uu____9084 =
                                           let uu____9085 =
                                             let uu____9088 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9088 in
                                           uu____9085.FStar_Syntax_Syntax.n in
                                         match uu____9084 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9089 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9093 =
                                               let uu____9094 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9094 in
                                             if uu____9093
                                             then fail kres
                                             else ()
                                         | uu____9096 -> fail kres);
                                        (let a =
                                           let uu____9098 =
                                             let uu____9101 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9101 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9098 kres in
                                         let t =
                                           let uu____9105 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9105
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
                      (fun uu____9224  ->
                         match uu____9224 with
                         | (lbname,e,c) ->
                             let uu____9270 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9339 ->
                                   let uu____9354 = (e, c) in
                                   (match uu____9354 with
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
                                                (fun uu____9391  ->
                                                   match uu____9391 with
                                                   | (x,uu____9399) ->
                                                       let uu____9404 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9404)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9414 =
                                                let uu____9415 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9415 in
                                              if uu____9414
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
                                          let uu____9423 =
                                            let uu____9424 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9424.FStar_Syntax_Syntax.n in
                                          match uu____9423 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9447 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9447 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9462 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9464 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9464, gen_tvars)) in
                             (match uu____9270 with
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
        (let uu____9610 = Obj.magic () in ());
        (let uu____9612 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9612
         then
           let uu____9613 =
             let uu____9614 =
               FStar_List.map
                 (fun uu____9627  ->
                    match uu____9627 with
                    | (lb,uu____9635,uu____9636) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9614 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9613
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9657  ->
                match uu____9657 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9686 = gen env is_rec lecs in
           match uu____9686 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9785  ->
                       match uu____9785 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9847 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____9847
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9891  ->
                           match uu____9891 with
                           | (l,us,e,c,gvs) ->
                               let uu____9925 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____9926 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____9927 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____9928 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____9929 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9925 uu____9926 uu____9927 uu____9928
                                 uu____9929))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9970  ->
                match uu____9970 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10014 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10014, t, c, gvs)) univnames_lecs
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
              (let uu____10057 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____10057 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10063 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10063) in
          let is_var e1 =
            let uu____10070 =
              let uu____10071 = FStar_Syntax_Subst.compress e1 in
              uu____10071.FStar_Syntax_Syntax.n in
            match uu____10070 with
            | FStar_Syntax_Syntax.Tm_name uu____10074 -> true
            | uu____10075 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___372_10091 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___372_10091.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___372_10091.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10092 -> e2 in
          let env2 =
            let uu___373_10094 = env1 in
            let uu____10095 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___373_10094.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___373_10094.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___373_10094.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___373_10094.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___373_10094.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___373_10094.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___373_10094.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___373_10094.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___373_10094.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___373_10094.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___373_10094.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___373_10094.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___373_10094.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___373_10094.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___373_10094.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10095;
              FStar_TypeChecker_Env.is_iface =
                (uu___373_10094.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___373_10094.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___373_10094.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___373_10094.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___373_10094.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___373_10094.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___373_10094.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___373_10094.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___373_10094.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___373_10094.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___373_10094.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___373_10094.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___373_10094.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___373_10094.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___373_10094.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___373_10094.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___373_10094.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___373_10094.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____10096 = check env2 t1 t2 in
          match uu____10096 with
          | FStar_Pervasives_Native.None  ->
              let uu____10103 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1 in
              let uu____10108 = FStar_TypeChecker_Env.get_range env2 in
              FStar_Errors.raise_error uu____10103 uu____10108
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10115 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10115
                then
                  let uu____10116 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10116
                else ());
               (let uu____10118 = decorate e t2 in (uu____10118, g)))
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
        let uu____10146 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10146
        then
          let uu____10151 = discharge g1 in
          let uu____10152 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10151, uu____10152)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10165 =
               let uu____10166 =
                 let uu____10167 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10167 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10166
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10165
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10169 = destruct_comp c1 in
           match uu____10169 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10186 = FStar_TypeChecker_Env.get_range env in
                 let uu____10187 =
                   let uu____10188 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10189 =
                     let uu____10190 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10191 =
                       let uu____10194 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10194] in
                     uu____10190 :: uu____10191 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10188 uu____10189 in
                 uu____10187 FStar_Pervasives_Native.None uu____10186 in
               ((let uu____10198 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10198
                 then
                   let uu____10199 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10199
                 else ());
                (let g2 =
                   let uu____10202 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10202 in
                 let uu____10203 = discharge g2 in
                 let uu____10204 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10203, uu____10204))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___332_10228 =
        match uu___332_10228 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10236)::[] -> f fst1
        | uu____10253 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10258 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10258
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10267 =
          let uu____10270 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10270 in
        FStar_All.pipe_right uu____10267
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10281 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10281
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___333_10295 =
        match uu___333_10295 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10303)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10322)::[] ->
            let uu____10351 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10351
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10356 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10366 =
          let uu____10373 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10373) in
        let uu____10378 =
          let uu____10387 =
            let uu____10394 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10394) in
          let uu____10399 =
            let uu____10408 =
              let uu____10415 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10415) in
            let uu____10420 =
              let uu____10429 =
                let uu____10436 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10436) in
              let uu____10441 =
                let uu____10450 =
                  let uu____10457 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10457) in
                [uu____10450; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10429 :: uu____10441 in
            uu____10408 :: uu____10420 in
          uu____10387 :: uu____10399 in
        uu____10366 :: uu____10378 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10508 =
            FStar_Util.find_map table
              (fun uu____10521  ->
                 match uu____10521 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10538 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10538
                     else FStar_Pervasives_Native.None) in
          (match uu____10508 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10541 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10545 =
      let uu____10546 = FStar_Syntax_Util.un_uinst l in
      uu____10546.FStar_Syntax_Syntax.n in
    match uu____10545 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10550 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10574)::uu____10575 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10586 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10593,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10594))::uu____10595 -> bs
      | uu____10612 ->
          let uu____10613 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10613 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10617 =
                 let uu____10618 = FStar_Syntax_Subst.compress t in
                 uu____10618.FStar_Syntax_Syntax.n in
               (match uu____10617 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10622) ->
                    let uu____10639 =
                      FStar_Util.prefix_until
                        (fun uu___334_10679  ->
                           match uu___334_10679 with
                           | (uu____10686,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10687)) ->
                               false
                           | uu____10690 -> true) bs' in
                    (match uu____10639 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10725,uu____10726) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10798,uu____10799) ->
                         let uu____10872 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10890  ->
                                   match uu____10890 with
                                   | (x,uu____10898) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10872
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10945  ->
                                     match uu____10945 with
                                     | (x,i) ->
                                         let uu____10964 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10964, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10974 -> bs))
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
          let uu____11006 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11006
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
        (let uu____11029 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11029
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11031 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11031))
         else ());
        (let fv =
           let uu____11034 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11034
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
         let uu____11042 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___374_11048 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___374_11048.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___374_11048.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___374_11048.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___374_11048.FStar_Syntax_Syntax.sigattrs)
           }), uu____11042))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___335_11058 =
        match uu___335_11058 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11059 -> false in
      let reducibility uu___336_11063 =
        match uu___336_11063 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11064 -> false in
      let assumption uu___337_11068 =
        match uu___337_11068 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11069 -> false in
      let reification uu___338_11073 =
        match uu___338_11073 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11074 -> true
        | uu____11075 -> false in
      let inferred uu___339_11079 =
        match uu___339_11079 with
        | FStar_Syntax_Syntax.Discriminator uu____11080 -> true
        | FStar_Syntax_Syntax.Projector uu____11081 -> true
        | FStar_Syntax_Syntax.RecordType uu____11086 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11095 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11104 -> false in
      let has_eq uu___340_11108 =
        match uu___340_11108 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11109 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11169 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11174 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11178 =
        let uu____11179 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___341_11183  ->
                  match uu___341_11183 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11184 -> false)) in
        FStar_All.pipe_right uu____11179 Prims.op_Negation in
      if uu____11178
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11197 =
            let uu____11202 =
              let uu____11203 = FStar_Syntax_Print.quals_to_string quals in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11203 msg in
            (FStar_Errors.QulifierListNotPermitted, uu____11202) in
          FStar_Errors.raise_error uu____11197 r in
        let err msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11211 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11215 =
            let uu____11216 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11216 in
          if uu____11215 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11221),uu____11222) ->
              ((let uu____11238 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11238
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11242 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11242
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11248 ->
              let uu____11257 =
                let uu____11258 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11258 in
              if uu____11257 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11264 ->
              let uu____11271 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11271 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11275 ->
              let uu____11282 =
                let uu____11283 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11283 in
              if uu____11282 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11289 ->
              let uu____11290 =
                let uu____11291 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11291 in
              if uu____11290 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11297 ->
              let uu____11298 =
                let uu____11299 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11299 in
              if uu____11298 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11305 ->
              let uu____11318 =
                let uu____11319 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11319 in
              if uu____11318 then err'1 () else ()
          | uu____11325 -> ()))
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
                          let uu____11388 =
                            let uu____11391 =
                              let uu____11392 =
                                let uu____11399 =
                                  let uu____11400 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11400 in
                                (uu____11399, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11392 in
                            FStar_Syntax_Syntax.mk uu____11391 in
                          uu____11388 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11441  ->
                                  match uu____11441 with
                                  | (x,imp) ->
                                      let uu____11452 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11452, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11454 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11454 in
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
                             let uu____11463 =
                               let uu____11464 =
                                 let uu____11465 =
                                   let uu____11466 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11467 =
                                     let uu____11468 =
                                       let uu____11469 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11469 in
                                     [uu____11468] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11466
                                     uu____11467 in
                                 uu____11465 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11464 in
                             FStar_Syntax_Util.refine x uu____11463 in
                           let uu____11472 =
                             let uu___375_11473 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___375_11473.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___375_11473.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11472) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11488 =
                          FStar_List.map
                            (fun uu____11510  ->
                               match uu____11510 with
                               | (x,uu____11522) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11488 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11571  ->
                                match uu____11571 with
                                | (x,uu____11583) ->
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
                             (let uu____11597 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11597)
                               ||
                               (let uu____11599 =
                                  let uu____11600 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11600.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11599) in
                           let quals =
                             let uu____11604 =
                               let uu____11607 =
                                 let uu____11610 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11610
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11614 =
                                 FStar_List.filter
                                   (fun uu___342_11618  ->
                                      match uu___342_11618 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11619 -> false) iquals in
                               FStar_List.append uu____11607 uu____11614 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11604 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11640 =
                                 let uu____11641 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11641 in
                               FStar_Syntax_Syntax.mk_Total uu____11640 in
                             let uu____11642 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11642 in
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
                           (let uu____11645 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11645
                            then
                              let uu____11646 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11646
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
                                             fun uu____11699  ->
                                               match uu____11699 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11723 =
                                                       let uu____11726 =
                                                         let uu____11727 =
                                                           let uu____11734 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11734,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11727 in
                                                       pos uu____11726 in
                                                     (uu____11723, b)
                                                   else
                                                     (let uu____11738 =
                                                        let uu____11741 =
                                                          let uu____11742 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11742 in
                                                        pos uu____11741 in
                                                      (uu____11738, b)))) in
                                   let pat_true =
                                     let uu____11760 =
                                       let uu____11763 =
                                         let uu____11764 =
                                           let uu____11777 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11777, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11764 in
                                       pos uu____11763 in
                                     (uu____11760,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____11811 =
                                       let uu____11814 =
                                         let uu____11815 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____11815 in
                                       pos uu____11814 in
                                     (uu____11811,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____11827 =
                                     let uu____11830 =
                                       let uu____11831 =
                                         let uu____11854 =
                                           let uu____11857 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____11858 =
                                             let uu____11861 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____11861] in
                                           uu____11857 :: uu____11858 in
                                         (arg_exp, uu____11854) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11831 in
                                     FStar_Syntax_Syntax.mk uu____11830 in
                                   uu____11827 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____11868 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____11868
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
                                let uu____11876 =
                                  let uu____11881 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____11881 in
                                let uu____11882 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____11876;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____11882
                                } in
                              let impl =
                                let uu____11886 =
                                  let uu____11887 =
                                    let uu____11894 =
                                      let uu____11897 =
                                        let uu____11898 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____11898
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____11897] in
                                    ((false, [lb]), uu____11894) in
                                  FStar_Syntax_Syntax.Sig_let uu____11887 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____11886;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____11916 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____11916
                               then
                                 let uu____11917 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____11917
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
                                fun uu____11959  ->
                                  match uu____11959 with
                                  | (a,uu____11965) ->
                                      let uu____11966 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____11966 with
                                       | (field_name,uu____11972) ->
                                           let field_proj_tm =
                                             let uu____11974 =
                                               let uu____11975 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____11975 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____11974 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____11992 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12024  ->
                                    match uu____12024 with
                                    | (x,uu____12032) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12034 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12034 with
                                         | (field_name,uu____12042) ->
                                             let t =
                                               let uu____12044 =
                                                 let uu____12045 =
                                                   let uu____12048 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12048 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12045 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12044 in
                                             let only_decl =
                                               (let uu____12052 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12052)
                                                 ||
                                                 (let uu____12054 =
                                                    let uu____12055 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12055.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12054) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12069 =
                                                   FStar_List.filter
                                                     (fun uu___343_12073  ->
                                                        match uu___343_12073
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12074 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12069
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___344_12087  ->
                                                         match uu___344_12087
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12088 ->
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
                                             ((let uu____12107 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12107
                                               then
                                                 let uu____12108 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12108
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
                                                           fun uu____12156 
                                                             ->
                                                             match uu____12156
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12180
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12180,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12196
                                                                    =
                                                                    let uu____12199
                                                                    =
                                                                    let uu____12200
                                                                    =
                                                                    let uu____12207
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12207,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12200 in
                                                                    pos
                                                                    uu____12199 in
                                                                    (uu____12196,
                                                                    b))
                                                                   else
                                                                    (let uu____12211
                                                                    =
                                                                    let uu____12214
                                                                    =
                                                                    let uu____12215
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12215 in
                                                                    pos
                                                                    uu____12214 in
                                                                    (uu____12211,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12231 =
                                                     let uu____12234 =
                                                       let uu____12235 =
                                                         let uu____12248 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12248,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12235 in
                                                     pos uu____12234 in
                                                   let uu____12257 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12231,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12257) in
                                                 let body =
                                                   let uu____12269 =
                                                     let uu____12272 =
                                                       let uu____12273 =
                                                         let uu____12296 =
                                                           let uu____12299 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12299] in
                                                         (arg_exp,
                                                           uu____12296) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12273 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12272 in
                                                   uu____12269
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12307 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12307
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
                                                   let uu____12314 =
                                                     let uu____12319 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12319 in
                                                   let uu____12320 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12314;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12320
                                                   } in
                                                 let impl =
                                                   let uu____12324 =
                                                     let uu____12325 =
                                                       let uu____12332 =
                                                         let uu____12335 =
                                                           let uu____12336 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12336
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12335] in
                                                       ((false, [lb]),
                                                         uu____12332) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12325 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12324;
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
                                                 (let uu____12354 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12354
                                                  then
                                                    let uu____12355 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12355
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____11992 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12395) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12400 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12400 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12422 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12422 with
                    | (formals,uu____12438) ->
                        let uu____12455 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12487 =
                                   let uu____12488 =
                                     let uu____12489 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12489 in
                                   FStar_Ident.lid_equals typ_lid uu____12488 in
                                 if uu____12487
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12508,uvs',tps,typ0,uu____12512,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12531 -> failwith "Impossible"
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
                                  (FStar_Errors.UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng in
                        (match uu____12455 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12604 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12604 with
                              | (indices,uu____12620) ->
                                  let refine_domain =
                                    let uu____12638 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___345_12643  ->
                                              match uu___345_12643 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12644 -> true
                                              | uu____12653 -> false)) in
                                    if uu____12638
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___346_12661 =
                                      match uu___346_12661 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12664,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12676 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12677 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12677 with
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
                                    let uu____12688 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12688 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12753  ->
                                               fun uu____12754  ->
                                                 match (uu____12753,
                                                         uu____12754)
                                                 with
                                                 | ((x,uu____12772),(x',uu____12774))
                                                     ->
                                                     let uu____12783 =
                                                       let uu____12790 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12790) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12783) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12791 -> []