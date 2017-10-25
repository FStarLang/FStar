open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let report:
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____19 = FStar_TypeChecker_Env.get_range env in
      let uu____20 = FStar_TypeChecker_Err.failed_to_prove_specification errs in
      FStar_Errors.err uu____19 uu____20
let is_type: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____25 =
      let uu____26 = FStar_Syntax_Subst.compress t in
      uu____26.FStar_Syntax_Syntax.n in
    match uu____25 with
    | FStar_Syntax_Syntax.Tm_type uu____29 -> true
    | uu____30 -> false
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
        let uu____75 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____77 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____77) in
        if uu____75
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env in
      let uu____79 = FStar_TypeChecker_Env.get_range env in
      FStar_TypeChecker_Rel.new_uvar uu____79 bs k
let new_uvar:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun k  ->
      let uu____88 = new_uvar_aux env k in
      FStar_Pervasives_Native.fst uu____88
let as_uvar: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___128_98  ->
    match uu___128_98 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____100);
        FStar_Syntax_Syntax.pos = uu____101;
        FStar_Syntax_Syntax.vars = uu____102;_} -> uv
    | uu____129 -> failwith "Impossible"
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
          let uu____158 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
          match uu____158 with
          | FStar_Pervasives_Native.Some (uu____181::(tm,uu____183)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____235 ->
              let uu____246 = new_uvar_aux env k in
              (match uu____246 with
               | (t,u) ->
                   let g =
                     let uu___147_266 = FStar_TypeChecker_Rel.trivial_guard in
                     let uu____267 =
                       let uu____282 =
                         let uu____295 = as_uvar u in
                         (reason, env, uu____295, t, k, r) in
                       [uu____282] in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___147_266.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___147_266.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___147_266.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____267
                     } in
                   let uu____320 =
                     let uu____327 =
                       let uu____332 = as_uvar u in (uu____332, r) in
                     [uu____327] in
                   (t, uu____320, g))
let check_uvars: FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t in
      let uu____362 =
        let uu____363 = FStar_Util.set_is_empty uvs in
        Prims.op_Negation uu____363 in
      if uu____362
      then
        let us =
          let uu____369 =
            let uu____372 = FStar_Util.set_elements uvs in
            FStar_List.map
              (fun uu____390  ->
                 match uu____390 with
                 | (x,uu____396) -> FStar_Syntax_Print.uvar_to_string x)
              uu____372 in
          FStar_All.pipe_right uu____369 (FStar_String.concat ", ") in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____403 =
            let uu____404 = FStar_Syntax_Print.term_to_string t in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____404 in
          FStar_Errors.err r uu____403);
         FStar_Options.pop ())
      else ()
let extract_let_rec_annotation:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____419  ->
      match uu____419 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____429;
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
                   let uu____475 =
                     let uu____476 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort in
                     uu____476.FStar_Syntax_Syntax.n in
                   match uu____475 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____483 = FStar_Syntax_Util.type_u () in
                       (match uu____483 with
                        | (k,uu____493) ->
                            let t2 =
                              let uu____495 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k in
                              FStar_All.pipe_right uu____495
                                FStar_Pervasives_Native.fst in
                            ((let uu___148_505 = a in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___148_505.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___148_505.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____506 -> (a, true) in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1 in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____543) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____550) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____613) ->
                       let uu____634 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____694  ->
                                 fun uu____695  ->
                                   match (uu____694, uu____695) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____773 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a in
                                       (match uu____773 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp) in
                                            let bs2 =
                                              FStar_List.append bs1 [b] in
                                            let scope1 =
                                              FStar_List.append scope [b] in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty)) in
                       (match uu____634 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____885 = aux must_check_ty1 scope body in
                            (match uu____885 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____914 =
                                         FStar_Options.ml_ish () in
                                       if uu____914
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c in
                                 ((let uu____921 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High in
                                   if uu____921
                                   then
                                     let uu____922 =
                                       FStar_Range.string_of_range r in
                                     let uu____923 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____924 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2 in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____922 uu____923 uu____924
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____934 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____948 =
                            let uu____953 =
                              let uu____954 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0 in
                              FStar_All.pipe_right uu____954
                                FStar_Pervasives_Native.fst in
                            FStar_Util.Inl uu____953 in
                          (uu____948, false)) in
                 let uu____967 =
                   let uu____976 = t_binders env in aux false uu____976 e in
                 match uu____967 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1001 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c in
                           if uu____1001
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1005 =
                                let uu____1006 =
                                  let uu____1011 =
                                    let uu____1012 =
                                      FStar_Syntax_Print.comp_to_string c in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____1012 in
                                  (uu____1011, rng) in
                                FStar_Errors.Error uu____1006 in
                              FStar_Exn.raise uu____1005)
                       | FStar_Util.Inl t3 -> t3 in
                     ([], t3, b)))
           | uu____1020 ->
               let uu____1021 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1 in
               (match uu____1021 with
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
              let uu____1086 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
              match uu____1086 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1087;
                  FStar_Syntax_Syntax.vars = uu____1088;_} ->
                  let uu____1091 = FStar_Syntax_Util.type_u () in
                  (match uu____1091 with | (t,uu____1097) -> new_uvar env1 t)
              | t -> tc_annot env1 t in
            let uu___149_1099 = x in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___149_1099.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___149_1099.FStar_Syntax_Syntax.index);
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
                  | uu____1164 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1172) ->
                let uu____1177 = FStar_Syntax_Util.type_u () in
                (match uu____1177 with
                 | (k,uu____1201) ->
                     let t = new_uvar env1 k in
                     let x1 =
                       let uu___150_1204 = x in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___150_1204.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___150_1204.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       } in
                     let uu____1205 =
                       let uu____1210 =
                         FStar_TypeChecker_Env.all_binders env1 in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1210 t in
                     (match uu____1205 with
                      | (e,u) ->
                          let p2 =
                            let uu___151_1234 = p1 in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___151_1234.FStar_Syntax_Syntax.p)
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
                let uu____1290 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1417  ->
                          fun uu____1418  ->
                            match (uu____1417, uu____1418) with
                            | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                                let uu____1607 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2 in
                                (match uu____1607 with
                                 | (b',a',w',env3,te,pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), ((pat, imp) :: pats1))))
                       ([], [], [], env1, [], [])) in
                (match uu____1290 with
                 | (b,a,w,env2,args,pats1) ->
                     let e =
                       let uu____1805 =
                         let uu____1808 =
                           let uu____1809 =
                             let uu____1816 =
                               let uu____1819 =
                                 let uu____1820 =
                                   FStar_Syntax_Syntax.fv_to_tm fv in
                                 let uu____1821 =
                                   FStar_All.pipe_right args FStar_List.rev in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1820
                                   uu____1821 in
                               uu____1819 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p in
                             (uu____1816,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app)) in
                           FStar_Syntax_Syntax.Tm_meta uu____1809 in
                         FStar_Syntax_Syntax.mk uu____1808 in
                       uu____1805 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p in
                     let uu____1833 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu____1844 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu____1855 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu____1833, uu____1844, uu____1855, env2, e,
                       (let uu___152_1877 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___152_1877.FStar_Syntax_Syntax.p)
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
                    (fun uu____1961  ->
                       match uu____1961 with
                       | (p2,imp) ->
                           let uu____1980 = elaborate_pat env1 p2 in
                           (uu____1980, imp)) pats in
                let uu____1985 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____1985 with
                 | (uu____1992,t) ->
                     let uu____1994 = FStar_Syntax_Util.arrow_formals t in
                     (match uu____1994 with
                      | (f,uu____2010) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2132::uu____2133) ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Too many pattern arguments",
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                            | (uu____2184::uu____2185,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2263  ->
                                        match uu____2263 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2290 =
                                                     let uu____2293 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1 in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2293 in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2290
                                                     FStar_Syntax_Syntax.tun in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                                 let uu____2295 =
                                                   maybe_dot inaccessible a r in
                                                 (uu____2295, true)
                                             | uu____2300 ->
                                                 let uu____2303 =
                                                   let uu____2304 =
                                                     let uu____2309 =
                                                       let uu____2310 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.format1
                                                         "Insufficient pattern arguments (%s)"
                                                         uu____2310 in
                                                     (uu____2309,
                                                       (FStar_Ident.range_of_lid
                                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                                                   FStar_Errors.Error
                                                     uu____2304 in
                                                 FStar_Exn.raise uu____2303)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2384,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2385)) when p_imp ->
                                     let uu____2388 = aux formals' pats' in
                                     (p2, true) :: uu____2388
                                 | (uu____2405,FStar_Pervasives_Native.Some
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
                                     let uu____2413 = aux formals' pats2 in
                                     (p3, true) :: uu____2413
                                 | (uu____2430,imp) ->
                                     let uu____2436 =
                                       let uu____2443 =
                                         FStar_Syntax_Syntax.is_implicit imp in
                                       (p2, uu____2443) in
                                     let uu____2446 = aux formals' pats' in
                                     uu____2436 :: uu____2446) in
                          let uu___153_2461 = p1 in
                          let uu____2464 =
                            let uu____2465 =
                              let uu____2478 = aux f pats1 in
                              (fv, uu____2478) in
                            FStar_Syntax_Syntax.Pat_cons uu____2465 in
                          {
                            FStar_Syntax_Syntax.v = uu____2464;
                            FStar_Syntax_Syntax.p =
                              (uu___153_2461.FStar_Syntax_Syntax.p)
                          }))
            | uu____2495 -> p1 in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu____2529 = pat_as_arg_with_env allow_wc_dependence env1 p2 in
            match uu____2529 with
            | (b,a,w,env2,arg,p3) ->
                let uu____2582 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu____2582 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2606 =
                       let uu____2607 =
                         let uu____2612 =
                           FStar_TypeChecker_Err.nonlinear_pattern_variable x in
                         (uu____2612, (p3.FStar_Syntax_Syntax.p)) in
                       FStar_Errors.Error uu____2607 in
                     FStar_Exn.raise uu____2606
                 | uu____2629 -> (b, a, w, arg, p3)) in
          let uu____2638 = one_pat true env p in
          match uu____2638 with
          | (b,uu____2664,uu____2665,tm,p1) -> (b, tm, p1)
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
          | (uu____2713,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2715)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2720,uu____2721) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2725 =
                    let uu____2726 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2727 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2726 uu____2727 in
                  failwith uu____2725)
               else ();
               (let uu____2730 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat") in
                if uu____2730
                then
                  let uu____2731 = FStar_Syntax_Print.bv_to_string x in
                  let uu____2732 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2731
                    uu____2732
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___154_2736 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___154_2736.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___154_2736.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2740 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation in
                if uu____2740
                then
                  let uu____2741 =
                    let uu____2742 = FStar_Syntax_Print.bv_to_string x in
                    let uu____2743 = FStar_Syntax_Print.bv_to_string y in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2742 uu____2743 in
                  failwith uu____2741
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort in
                let x1 =
                  let uu___155_2747 = x in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___155_2747.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___155_2747.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  } in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2749),uu____2750) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2772 =
                  let uu____2773 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  Prims.op_Negation uu____2773 in
                if uu____2772
                then
                  let uu____2774 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2774
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2793;
                FStar_Syntax_Syntax.vars = uu____2794;_},args))
              ->
              ((let uu____2833 =
                  let uu____2834 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____2834 Prims.op_Negation in
                if uu____2833
                then
                  let uu____2835 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____2835
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2971)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3046) ->
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
                       | ((e2,imp),uu____3083) ->
                           let pat =
                             let uu____3105 = aux argpat e2 in
                             let uu____3106 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3105, uu____3106) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3111 ->
                      let uu____3134 =
                        let uu____3135 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3136 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3135 uu____3136 in
                      failwith uu____3134 in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3148;
                     FStar_Syntax_Syntax.vars = uu____3149;_},uu____3150);
                FStar_Syntax_Syntax.pos = uu____3151;
                FStar_Syntax_Syntax.vars = uu____3152;_},args))
              ->
              ((let uu____3195 =
                  let uu____3196 = FStar_Syntax_Syntax.fv_eq fv fv' in
                  FStar_All.pipe_right uu____3196 Prims.op_Negation in
                if uu____3195
                then
                  let uu____3197 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                  failwith uu____3197
                else ());
               (let fv1 = fv' in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3333)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3408) ->
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
                       | ((e2,imp),uu____3445) ->
                           let pat =
                             let uu____3467 = aux argpat e2 in
                             let uu____3468 =
                               FStar_Syntax_Syntax.is_implicit imp in
                             (uu____3467, uu____3468) in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3473 ->
                      let uu____3496 =
                        let uu____3497 = FStar_Syntax_Print.pat_to_string p1 in
                        let uu____3498 = FStar_Syntax_Print.term_to_string e1 in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3497 uu____3498 in
                      failwith uu____3496 in
                match_args [] args argpats))
          | uu____3507 ->
              let uu____3512 =
                let uu____3513 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p in
                let uu____3514 = FStar_Syntax_Print.pat_to_string qq in
                let uu____3515 = FStar_Syntax_Print.term_to_string exp in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3513 uu____3514 uu____3515 in
              failwith uu____3512 in
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
    let pat_as_arg uu____3553 =
      match uu____3553 with
      | (p,i) ->
          let uu____3570 = decorated_pattern_as_term p in
          (match uu____3570 with
           | (vars,te) ->
               let uu____3593 =
                 let uu____3598 = FStar_Syntax_Syntax.as_implicit i in
                 (te, uu____3598) in
               (vars, uu____3593)) in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3612 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
        ([], uu____3612)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3616 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3616)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3620 = mk1 (FStar_Syntax_Syntax.Tm_name x) in
        ([x], uu____3620)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3641 =
          let uu____3656 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg) in
          FStar_All.pipe_right uu____3656 FStar_List.unzip in
        (match uu____3641 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars in
             let uu____3766 =
               let uu____3767 =
                 let uu____3768 =
                   let uu____3783 = FStar_Syntax_Syntax.fv_to_tm fv in
                   (uu____3783, args) in
                 FStar_Syntax_Syntax.Tm_app uu____3768 in
               mk1 uu____3767 in
             (vars1, uu____3766))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
let destruct_comp:
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3824)::[] -> wp
      | uu____3841 ->
          let uu____3850 =
            let uu____3851 =
              let uu____3852 =
                FStar_List.map
                  (fun uu____3862  ->
                     match uu____3862 with
                     | (x,uu____3868) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args in
              FStar_All.pipe_right uu____3852 (FStar_String.concat ", ") in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3851 in
          failwith uu____3850 in
    let uu____3873 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____3873, (c.FStar_Syntax_Syntax.result_typ), wp)
let lift_comp:
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3890 = destruct_comp c in
        match uu____3890 with
        | (u,uu____3898,wp) ->
            let uu____3900 =
              let uu____3909 =
                let uu____3910 =
                  lift.FStar_TypeChecker_Env.mlift_wp
                    c.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____3910 in
              [uu____3909] in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3900;
              FStar_Syntax_Syntax.flags = []
            }
let join_effects:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3923 =
          let uu____3930 = FStar_TypeChecker_Env.norm_eff_name env l1 in
          let uu____3931 = FStar_TypeChecker_Env.norm_eff_name env l2 in
          FStar_TypeChecker_Env.join env uu____3930 uu____3931 in
        match uu____3923 with | (m,uu____3933,uu____3934) -> m
let join_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3947 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2) in
        if uu____3947
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
        let uu____3987 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name in
        match uu____3987 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1 in
            let m2 = lift_comp c21 m lift2 in
            let md = FStar_TypeChecker_Env.get_effect_decl env m in
            let uu____4024 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname in
            (match uu____4024 with
             | (a,kwp) ->
                 let uu____4055 = destruct_comp m1 in
                 let uu____4062 = destruct_comp m2 in
                 ((md, a, kwp), uu____4055, uu____4062))
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
            let uu____4133 =
              let uu____4134 =
                let uu____4143 = FStar_Syntax_Syntax.as_arg wp in
                [uu____4143] in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4134;
                FStar_Syntax_Syntax.flags = flags
              } in
            FStar_Syntax_Syntax.mk_Comp uu____4133
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
      let uu___156_4193 = lc in
      let uu____4194 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___156_4193.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4194;
        FStar_Syntax_Syntax.cflags =
          (uu___156_4193.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4199  ->
             let uu____4200 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Subst.subst_comp subst1 uu____4200)
      }
let is_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4205 =
      let uu____4206 = FStar_Syntax_Subst.compress t in
      uu____4206.FStar_Syntax_Syntax.n in
    match uu____4205 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4209 -> true
    | uu____4222 -> false
let close_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4239 = FStar_Syntax_Util.is_ml_comp c in
        if uu____4239
        then c
        else
          (let uu____4241 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
           if uu____4241
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4280 = FStar_Syntax_Syntax.mk_binder x in
                         [uu____4280] in
                       let us =
                         let uu____4284 =
                           let uu____4287 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort in
                           [uu____4287] in
                         u_res :: uu____4284 in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL])) in
                       let uu____4291 =
                         let uu____4292 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp in
                         let uu____4293 =
                           let uu____4294 = FStar_Syntax_Syntax.as_arg res_t in
                           let uu____4295 =
                             let uu____4298 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort in
                             let uu____4299 =
                               let uu____4302 =
                                 FStar_Syntax_Syntax.as_arg wp1 in
                               [uu____4302] in
                             uu____4298 :: uu____4299 in
                           uu____4294 :: uu____4295 in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4292 uu____4293 in
                       uu____4291 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
              let uu____4306 = destruct_comp c1 in
              match uu____4306 with
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
        let close1 uu____4337 =
          let uu____4338 = lc.FStar_Syntax_Syntax.comp () in
          close_comp env bvs uu____4338 in
        let uu___157_4339 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___157_4339.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___157_4339.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___157_4339.FStar_Syntax_Syntax.cflags);
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
          let uu____4353 =
            (let uu____4356 =
               FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid in
             FStar_All.pipe_left Prims.op_Negation uu____4356) ||
              (FStar_Syntax_Util.is_unit t) in
          if uu____4353
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4361 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4361
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4363 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4363 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____4371 =
                        let uu____4372 =
                          let uu____4373 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____4374 =
                            let uu____4375 = FStar_Syntax_Syntax.as_arg t in
                            let uu____4376 =
                              let uu____4379 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____4379] in
                            uu____4375 :: uu____4376 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4373 uu____4374 in
                        uu____4372 FStar_Pervasives_Native.None
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.NoFullNorm] env
                        uu____4371) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____4383 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4383
         then
           let uu____4384 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4385 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4386 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4384
             uu____4385 uu____4386
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
          fun uu____4409  ->
            match uu____4409 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4422 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4422
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4425 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4427 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4428 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4425 uu____4427 bstr uu____4428
                  else ());
                 (let bind_it uu____4433 =
                    let uu____4434 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4434
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4444 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4444
                        then
                          let uu____4445 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4447 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4448 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4449 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4450 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4445 uu____4447 uu____4448 uu____4449
                            uu____4450
                        else ());
                       (let try_simplify uu____4465 =
                          let aux uu____4479 =
                            let uu____4480 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4480
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4509 ->
                                  let uu____4510 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4510
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4537 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4537
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4593 =
                                  let uu____4598 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4598, reason) in
                                FStar_Util.Inl uu____4593
                            | uu____4603 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4622 =
                              let uu____4623 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4623.FStar_Syntax_Syntax.n in
                            match uu____4622 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4627) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4633 -> c in
                          let uu____4634 =
                            let uu____4635 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4635 in
                          if uu____4634
                          then
                            let uu____4648 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4648
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4668 =
                                  let uu____4669 =
                                    let uu____4674 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4674) in
                                  FStar_Errors.Error uu____4669 in
                                FStar_Exn.raise uu____4668))
                          else
                            (let uu____4686 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4686
                             then subst_c2 "both total"
                             else
                               (let uu____4698 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4698
                                then
                                  let uu____4709 =
                                    let uu____4714 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4714, "both gtot") in
                                  FStar_Util.Inl uu____4709
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4740 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4742 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4742) in
                                       if uu____4740
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___158_4755 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___158_4755.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___158_4755.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4756 =
                                           let uu____4761 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4761, "c1 Tot") in
                                         FStar_Util.Inl uu____4756
                                       else aux ()
                                   | uu____4767 -> aux ()))) in
                        let uu____4776 = try_simplify () in
                        match uu____4776 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4800 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4800
                              then
                                let uu____4801 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4802 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4803 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4801 uu____4802 uu____4803
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4812 = lift_and_destruct env c1 c2 in
                            (match uu____4812 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4869 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4869]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4871 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4871] in
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
                                   let uu____4884 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4885 =
                                     let uu____4888 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4889 =
                                       let uu____4892 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4893 =
                                         let uu____4896 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4897 =
                                           let uu____4900 =
                                             let uu____4901 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4901 in
                                           [uu____4900] in
                                         uu____4896 :: uu____4897 in
                                       uu____4892 :: uu____4893 in
                                     uu____4888 :: uu____4889 in
                                   uu____4884 :: uu____4885 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4906 =
                                     let uu____4907 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4907
                                       wp_args in
                                   uu____4906 FStar_Pervasives_Native.None
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
              let uu____4954 =
                let uu____4955 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4955 in
              if uu____4954
              then f
              else (let uu____4957 = reason1 () in label uu____4957 r f)
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
            let uu___159_4971 = g in
            let uu____4972 =
              let uu____4973 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4973 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4972;
              FStar_TypeChecker_Env.deferred =
                (uu___159_4971.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___159_4971.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___159_4971.FStar_TypeChecker_Env.implicits)
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
      | uu____4985 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5007 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5011 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5011
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5018 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5018
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5023 = destruct_comp c1 in
                    match uu____5023 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5039 =
                            let uu____5040 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5041 =
                              let uu____5042 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5043 =
                                let uu____5046 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5047 =
                                  let uu____5050 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5050] in
                                uu____5046 :: uu____5047 in
                              uu____5042 :: uu____5043 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5040
                              uu____5041 in
                          uu____5039 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___160_5053 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___160_5053.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___160_5053.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___160_5053.FStar_Syntax_Syntax.cflags);
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
            let uu____5091 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5091
            then (lc, g0)
            else
              ((let uu____5098 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5098
                then
                  let uu____5099 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5100 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5099 uu____5100
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___129_5110  ->
                          match uu___129_5110 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5113 -> [])) in
                let strengthen uu____5119 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5127 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5127 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5134 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5136 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5136) in
                           if uu____5134
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5143 =
                                 let uu____5144 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5144 in
                               FStar_Syntax_Util.comp_set_flags uu____5143
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5150 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5150
                           then
                             let uu____5151 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5152 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5151 uu____5152
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5155 = destruct_comp c2 in
                           match uu____5155 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5171 =
                                   let uu____5172 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5173 =
                                     let uu____5174 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5175 =
                                       let uu____5178 =
                                         let uu____5179 =
                                           let uu____5180 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5180 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5179 in
                                       let uu____5181 =
                                         let uu____5184 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5184] in
                                       uu____5178 :: uu____5181 in
                                     uu____5174 :: uu____5175 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5172
                                     uu____5173 in
                                 uu____5171 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5188 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5188
                                 then
                                   let uu____5189 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5189
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5192 =
                  let uu___161_5193 = lc in
                  let uu____5194 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5195 =
                    let uu____5198 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5200 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5200) in
                    if uu____5198 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5194;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___161_5193.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5195;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5192,
                  (let uu___162_5205 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___162_5205.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___162_5205.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___162_5205.FStar_TypeChecker_Env.implicits)
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
        let uu____5223 =
          let uu____5228 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5229 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5228, uu____5229) in
        match uu____5223 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5238 =
                let uu____5239 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5240 =
                  let uu____5241 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5242 =
                    let uu____5245 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5245] in
                  uu____5241 :: uu____5242 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5239 uu____5240 in
              uu____5238 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5251 =
                let uu____5252 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5253 =
                  let uu____5254 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5255 =
                    let uu____5258 =
                      let uu____5259 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5259 in
                    let uu____5260 =
                      let uu____5263 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5263] in
                    uu____5258 :: uu____5260 in
                  uu____5254 :: uu____5255 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5252 uu____5253 in
              uu____5251 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5269 =
                let uu____5270 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5271 =
                  let uu____5272 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5273 =
                    let uu____5276 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5277 =
                      let uu____5280 =
                        let uu____5281 =
                          let uu____5282 =
                            let uu____5283 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5283] in
                          FStar_Syntax_Util.abs uu____5282 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5281 in
                      [uu____5280] in
                    uu____5276 :: uu____5277 in
                  uu____5272 :: uu____5273 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5270 uu____5271 in
              uu____5269 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5290 = FStar_TypeChecker_Env.get_range env in
              bind uu____5290 env FStar_Pervasives_Native.None
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
          let comp uu____5313 =
            let uu____5314 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5314
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5317 =
                 let uu____5342 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5343 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5342 uu____5343 in
               match uu____5317 with
               | ((md,uu____5345,uu____5346),(u_res_t,res_t,wp_then),
                  (uu____5350,uu____5351,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5389 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5390 =
                       let uu____5391 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5392 =
                         let uu____5393 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5394 =
                           let uu____5397 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5398 =
                             let uu____5401 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5402 =
                               let uu____5405 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5405] in
                             uu____5401 :: uu____5402 in
                           uu____5397 :: uu____5398 in
                         uu____5393 :: uu____5394 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5391 uu____5392 in
                     uu____5390 FStar_Pervasives_Native.None uu____5389 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5411 =
                     let uu____5412 = FStar_Options.split_cases () in
                     uu____5412 > (Prims.parse_int "0") in
                   if uu____5411
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5418 =
                          let uu____5419 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5420 =
                            let uu____5421 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5422 =
                              let uu____5425 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5425] in
                            uu____5421 :: uu____5422 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5419 uu____5420 in
                        uu____5418 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5428 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5428;
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
      let uu____5437 =
        let uu____5438 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5438 in
      FStar_Syntax_Syntax.fvar uu____5437 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5473  ->
                 match uu____5473 with
                 | (uu____5478,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5483 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5485 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5485
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5505 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5506 =
                 let uu____5507 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5508 =
                   let uu____5509 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5510 =
                     let uu____5513 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5514 =
                       let uu____5517 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5518 =
                         let uu____5521 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5521] in
                       uu____5517 :: uu____5518 in
                     uu____5513 :: uu____5514 in
                   uu____5509 :: uu____5510 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5507 uu____5508 in
               uu____5506 FStar_Pervasives_Native.None uu____5505 in
             let default_case =
               let post_k =
                 let uu____5528 =
                   let uu____5535 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5535] in
                 let uu____5536 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5528 uu____5536 in
               let kwp =
                 let uu____5542 =
                   let uu____5549 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5549] in
                 let uu____5550 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5542 uu____5550 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5555 =
                   let uu____5556 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5556] in
                 let uu____5557 =
                   let uu____5558 =
                     let uu____5561 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5561 in
                   let uu____5562 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5558 uu____5562 in
                 FStar_Syntax_Util.abs uu____5555 uu____5557
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
                 (fun uu____5586  ->
                    fun celse  ->
                      match uu____5586 with
                      | (g,cthen) ->
                          let uu____5594 =
                            let uu____5619 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5619 celse in
                          (match uu____5594 with
                           | ((md,uu____5621,uu____5622),(uu____5623,uu____5624,wp_then),
                              (uu____5626,uu____5627,wp_else)) ->
                               let uu____5647 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5647 []))
                 lcases default_case in
             let uu____5648 =
               let uu____5649 = FStar_Options.split_cases () in
               uu____5649 > (Prims.parse_int "0") in
             if uu____5648
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5653 = destruct_comp comp1 in
                match uu____5653 with
                | (uu____5660,uu____5661,wp) ->
                    let wp1 =
                      let uu____5666 =
                        let uu____5667 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5668 =
                          let uu____5669 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5670 =
                            let uu____5673 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5673] in
                          uu____5669 :: uu____5670 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5667 uu____5668 in
                      uu____5666 FStar_Pervasives_Native.None
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
          let uu____5691 =
            ((let uu____5694 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5694) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5696 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5696) in
          if uu____5691
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5705 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5709 =
            (let uu____5712 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____5712) || env.FStar_TypeChecker_Env.lax in
          if uu____5709
          then c
          else
            (let uu____5716 = FStar_Syntax_Util.is_partial_return c in
             if uu____5716
             then c
             else
               (let uu____5720 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5720
                then
                  let uu____5723 =
                    let uu____5724 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5724 in
                  (if uu____5723
                   then
                     let uu____5727 =
                       let uu____5728 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5729 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5728 uu____5729 in
                     failwith uu____5727
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5734 =
                        let uu____5735 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5735 in
                      if uu____5734
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___163_5740 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___163_5740.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___163_5740.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___163_5740.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5751 =
                       let uu____5754 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5754
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5751 in
                   let eq1 =
                     let uu____5758 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5758 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5760 =
                     let uu____5761 =
                       let uu____5766 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5766.FStar_Syntax_Syntax.comp in
                     uu____5761 () in
                   FStar_Syntax_Util.comp_set_flags uu____5760 flags))) in
        let uu___164_5769 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___164_5769.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___164_5769.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = refine1
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
          let uu____5798 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5798 with
          | FStar_Pervasives_Native.None  ->
              let uu____5807 =
                let uu____5808 =
                  let uu____5813 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5814 = FStar_TypeChecker_Env.get_range env in
                  (uu____5813, uu____5814) in
                FStar_Errors.Error uu____5808 in
              FStar_Exn.raise uu____5807
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
            let uu____5851 =
              let uu____5852 = FStar_Syntax_Subst.compress t2 in
              uu____5852.FStar_Syntax_Syntax.n in
            match uu____5851 with
            | FStar_Syntax_Syntax.Tm_type uu____5855 -> true
            | uu____5856 -> false in
          let uu____5857 =
            let uu____5858 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5858.FStar_Syntax_Syntax.n in
          match uu____5857 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5866 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5877 =
                  let uu____5878 =
                    let uu____5879 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5879 in
                  (FStar_Pervasives_Native.None, uu____5878) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5877 in
              let e1 =
                let uu____5889 =
                  let uu____5890 =
                    let uu____5891 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5891] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5890 in
                uu____5889 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5896 -> (e, lc)
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
              (let uu____5929 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5929 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5952 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5974 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5974, false)
            else
              (let uu____5980 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5980, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____5991) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6000 =
                  let uu____6001 =
                    let uu____6006 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6006, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____6001 in
                FStar_Exn.raise uu____6000
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___165_6016 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___165_6016.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___165_6016.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___165_6016.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6021 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6021 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___166_6029 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___166_6029.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___166_6029.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___166_6029.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___167_6032 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___167_6032.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___167_6032.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___167_6032.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6038 =
                     let uu____6039 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6039
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6044 =
                          let uu____6045 = FStar_Syntax_Subst.compress f1 in
                          uu____6045.FStar_Syntax_Syntax.n in
                        match uu____6044 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6050,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6052;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6053;_},uu____6054)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___168_6076 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___168_6076.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___168_6076.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___168_6076.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6077 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6082 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6082
                              then
                                let uu____6083 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6084 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6085 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6086 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6083 uu____6084 uu____6085 uu____6086
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6089 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6089 with
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
                                  let uu____6102 = destruct_comp ct in
                                  (match uu____6102 with
                                   | (u_t,uu____6112,uu____6113) ->
                                       let wp =
                                         let uu____6117 =
                                           let uu____6118 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6119 =
                                             let uu____6120 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6121 =
                                               let uu____6124 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6124] in
                                             uu____6120 :: uu____6121 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6118 uu____6119 in
                                         uu____6117
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6128 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6128 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6138 =
                                             let uu____6139 =
                                               let uu____6140 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6140] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6139 in
                                           uu____6138
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6144 =
                                         let uu____6149 =
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6162 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6163 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6149
                                           uu____6162 e cret uu____6163 in
                                       (match uu____6144 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___169_6169 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___169_6169.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___169_6169.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6171 =
                                                let uu____6172 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6172 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6171
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6183 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6183
                                              then
                                                let uu____6184 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6184
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___130_6194  ->
                             match uu___130_6194 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6197 -> [])) in
                   let lc1 =
                     let uu___170_6199 = lc in
                     let uu____6200 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6200;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___171_6202 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___171_6202.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___171_6202.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___171_6202.FStar_TypeChecker_Env.implicits)
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
        let uu____6227 =
          let uu____6228 =
            let uu____6229 =
              let uu____6230 =
                let uu____6231 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6231 in
              [uu____6230] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6229 in
          uu____6228 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6227 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6238 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6238
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6256 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6271 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6300)::(ens,uu____6302)::uu____6303 ->
                    let uu____6332 =
                      let uu____6335 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6335 in
                    let uu____6336 =
                      let uu____6337 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6337 in
                    (uu____6332, uu____6336)
                | uu____6340 ->
                    let uu____6349 =
                      let uu____6350 =
                        let uu____6355 =
                          let uu____6356 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6356 in
                        (uu____6355, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6350 in
                    FStar_Exn.raise uu____6349)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6372)::uu____6373 ->
                    let uu____6392 =
                      let uu____6397 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6397 in
                    (match uu____6392 with
                     | (us_r,uu____6429) ->
                         let uu____6430 =
                           let uu____6435 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6435 in
                         (match uu____6430 with
                          | (us_e,uu____6467) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6470 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6470
                                  us_r in
                              let as_ens =
                                let uu____6472 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6472
                                  us_e in
                              let req =
                                let uu____6476 =
                                  let uu____6477 =
                                    let uu____6478 =
                                      let uu____6489 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6489] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6478 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6477 in
                                uu____6476 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6507 =
                                  let uu____6508 =
                                    let uu____6509 =
                                      let uu____6520 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6520] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6509 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6508 in
                                uu____6507 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6535 =
                                let uu____6538 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6538 in
                              let uu____6539 =
                                let uu____6540 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6540 in
                              (uu____6535, uu____6539)))
                | uu____6543 -> failwith "Impossible"))
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
      (let uu____6571 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6571
       then
         let uu____6572 = FStar_Syntax_Print.term_to_string tm in
         let uu____6573 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6572 uu____6573
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
        (let uu____6594 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6594
         then
           let uu____6595 = FStar_Syntax_Print.term_to_string tm in
           let uu____6596 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6595
             uu____6596
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6602 =
      let uu____6603 =
        let uu____6604 = FStar_Syntax_Subst.compress t in
        uu____6604.FStar_Syntax_Syntax.n in
      match uu____6603 with
      | FStar_Syntax_Syntax.Tm_app uu____6607 -> false
      | uu____6622 -> true in
    if uu____6602
    then t
    else
      (let uu____6624 = FStar_Syntax_Util.head_and_args t in
       match uu____6624 with
       | (head1,args) ->
           let uu____6661 =
             let uu____6662 =
               let uu____6663 = FStar_Syntax_Subst.compress head1 in
               uu____6663.FStar_Syntax_Syntax.n in
             match uu____6662 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6666 -> false in
           if uu____6661
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6688 ->
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
             let uu____6728 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6728 with
             | (formals,uu____6742) ->
                 let n_implicits =
                   let uu____6760 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6836  ->
                             match uu____6836 with
                             | (uu____6843,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6760 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6974 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6974 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____6998 =
                     let uu____6999 =
                       let uu____7004 =
                         let uu____7005 = FStar_Util.string_of_int n_expected in
                         let uu____7012 = FStar_Syntax_Print.term_to_string e in
                         let uu____7013 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7005 uu____7012 uu____7013 in
                       let uu____7020 = FStar_TypeChecker_Env.get_range env in
                       (uu____7004, uu____7020) in
                     FStar_Errors.Error uu____6999 in
                   FStar_Exn.raise uu____6998
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___131_7041 =
             match uu___131_7041 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7071 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7071 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7180) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7223,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7256 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7256 with
                           | (v1,uu____7296,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7313 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7313 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7406 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7406)))
                      | (uu____7433,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7479 =
                      let uu____7506 = inst_n_binders t in
                      aux [] uu____7506 bs1 in
                    (match uu____7479 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7577) -> (e, torig, guard)
                          | (uu____7608,[]) when
                              let uu____7639 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7639 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7640 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7672 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7687 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7696 =
      let uu____7699 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7699
        (FStar_List.map
           (fun u  ->
              let uu____7709 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7709 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7696 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7728 = FStar_Util.set_is_empty x in
      if uu____7728
      then []
      else
        (let s =
           let uu____7735 =
             let uu____7738 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7738 in
           FStar_All.pipe_right uu____7735 FStar_Util.set_elements in
         (let uu____7746 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7746
          then
            let uu____7747 =
              let uu____7748 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7748 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7747
          else ());
         (let r =
            let uu____7755 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7755 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7770 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7770
                     then
                       let uu____7771 =
                         let uu____7772 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7772 in
                       let uu____7773 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7774 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7771 uu____7773 uu____7774
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
        let uu____7798 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7798 FStar_Util.fifo_set_elements in
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
        | ([],uu____7833) -> generalized_univ_names
        | (uu____7840,[]) -> explicit_univ_names
        | uu____7847 ->
            let uu____7856 =
              let uu____7857 =
                let uu____7862 =
                  let uu____7863 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7863 in
                (uu____7862, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7857 in
            FStar_Exn.raise uu____7856
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
      (let uu____7882 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7882
       then
         let uu____7883 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7883
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7889 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7889
        then
          let uu____7890 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7890
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
        let uu____7963 =
          let uu____7964 =
            FStar_Util.for_all
              (fun uu____7977  ->
                 match uu____7977 with
                 | (uu____7986,uu____7987,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7964 in
        if uu____7963
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8033 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8033
              then
                let uu____8034 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8034
              else ());
             (let c1 =
                let uu____8037 = FStar_TypeChecker_Env.should_verify env in
                if uu____8037
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
              (let uu____8040 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8040
               then
                 let uu____8041 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8041
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8102 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8102 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8232 =
             match uu____8232 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8298 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8298
                   then
                     let uu____8299 =
                       let uu____8300 =
                         let uu____8303 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8303
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8300
                         (FStar_String.concat ", ") in
                     let uu____8330 =
                       let uu____8331 =
                         let uu____8334 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8334
                           (FStar_List.map
                              (fun uu____8362  ->
                                 match uu____8362 with
                                 | (u,t2) ->
                                     let uu____8369 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8370 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8369 uu____8370)) in
                       FStar_All.pipe_right uu____8331
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8299
                       uu____8330
                   else ());
                  (let univs2 =
                     let uu____8377 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8400  ->
                            match uu____8400 with
                            | (uu____8409,t2) ->
                                let uu____8411 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8411)
                       univs1 uu____8377 in
                   let uvs = gen_uvars uvt in
                   (let uu____8434 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8434
                    then
                      let uu____8435 =
                        let uu____8436 =
                          let uu____8439 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8439
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8436
                          (FStar_String.concat ", ") in
                      let uu____8466 =
                        let uu____8467 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8499  ->
                                  match uu____8499 with
                                  | (u,t2) ->
                                      let uu____8506 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8507 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8506 uu____8507)) in
                        FStar_All.pipe_right uu____8467
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8435
                        uu____8466
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8537 =
             let uu____8570 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8570 in
           match uu____8537 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8688 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8688
                 then ()
                 else
                   (let uu____8690 = lec_hd in
                    match uu____8690 with
                    | (lb1,uu____8698,uu____8699) ->
                        let uu____8700 = lec2 in
                        (match uu____8700 with
                         | (lb2,uu____8708,uu____8709) ->
                             let msg =
                               let uu____8711 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8712 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8711 uu____8712 in
                             let uu____8713 =
                               let uu____8714 =
                                 let uu____8719 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8719) in
                               FStar_Errors.Error uu____8714 in
                             FStar_Exn.raise uu____8713)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8830  ->
                           match uu____8830 with
                           | (u,uu____8838) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8860  ->
                                       match uu____8860 with
                                       | (u',uu____8868) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8873 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8873
                 then ()
                 else
                   (let uu____8875 = lec_hd in
                    match uu____8875 with
                    | (lb1,uu____8883,uu____8884) ->
                        let uu____8885 = lec2 in
                        (match uu____8885 with
                         | (lb2,uu____8893,uu____8894) ->
                             let msg =
                               let uu____8896 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8897 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8896 uu____8897 in
                             let uu____8898 =
                               let uu____8899 =
                                 let uu____8904 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8904) in
                               FStar_Errors.Error uu____8899 in
                             FStar_Exn.raise uu____8898)) in
               let lecs1 =
                 let uu____8914 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8973 = univs_and_uvars_of_lec this_lec in
                        match uu____8973 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8914 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9126 = lec_hd in
                   match uu____9126 with
                   | (lbname,e,c) ->
                       let uu____9136 =
                         let uu____9137 =
                           let uu____9142 =
                             let uu____9143 =
                               FStar_Syntax_Print.term_to_string k in
                             let uu____9144 =
                               FStar_Syntax_Print.lbname_to_string lbname in
                             let uu____9145 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Util.comp_result c) in
                             FStar_Util.format3
                               "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                               uu____9143 uu____9144 uu____9145 in
                           let uu____9146 =
                             FStar_TypeChecker_Env.get_range env in
                           (uu____9142, uu____9146) in
                         FStar_Errors.Error uu____9137 in
                       FStar_Exn.raise uu____9136 in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9176  ->
                         match uu____9176 with
                         | (u,k) ->
                             let uu____9189 = FStar_Syntax_Unionfind.find u in
                             (match uu____9189 with
                              | FStar_Pervasives_Native.Some uu____9198 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9205 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9209 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9209 with
                                   | (bs,kres) ->
                                       ((let uu____9247 =
                                           let uu____9248 =
                                             let uu____9251 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres in
                                             FStar_Syntax_Util.unrefine
                                               uu____9251 in
                                           uu____9248.FStar_Syntax_Syntax.n in
                                         match uu____9247 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9252 ->
                                             let free =
                                               FStar_Syntax_Free.names kres in
                                             let uu____9256 =
                                               let uu____9257 =
                                                 FStar_Util.set_is_empty free in
                                               Prims.op_Negation uu____9257 in
                                             if uu____9256
                                             then fail kres
                                             else ()
                                         | uu____9259 -> fail kres);
                                        (let a =
                                           let uu____9261 =
                                             let uu____9264 =
                                               FStar_TypeChecker_Env.get_range
                                                 env in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9264 in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9261 kres in
                                         let t =
                                           let uu____9268 =
                                             FStar_Syntax_Syntax.bv_to_name a in
                                           FStar_Syntax_Util.abs bs
                                             uu____9268
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
                      (fun uu____9387  ->
                         match uu____9387 with
                         | (lbname,e,c) ->
                             let uu____9433 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9502 ->
                                   let uu____9517 = (e, c) in
                                   (match uu____9517 with
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
                                                (fun uu____9554  ->
                                                   match uu____9554 with
                                                   | (x,uu____9562) ->
                                                       let uu____9567 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9567)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9577 =
                                                let uu____9578 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9578 in
                                              if uu____9577
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
                                          let uu____9586 =
                                            let uu____9587 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9587.FStar_Syntax_Syntax.n in
                                          match uu____9586 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9610 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9610 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9625 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9627 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9627, gen_tvars)) in
                             (match uu____9433 with
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
        (let uu____9776 = Obj.magic () in ());
        (let uu____9778 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9778
         then
           let uu____9779 =
             let uu____9780 =
               FStar_List.map
                 (fun uu____9793  ->
                    match uu____9793 with
                    | (lb,uu____9801,uu____9802) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9780 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9779
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9823  ->
                match uu____9823 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9852 = gen env is_rec lecs in
           match uu____9852 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9951  ->
                       match uu____9951 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10013 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____10013
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10057  ->
                           match uu____10057 with
                           | (l,us,e,c,gvs) ->
                               let uu____10091 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____10092 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____10093 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____10094 =
                                 FStar_Syntax_Print.term_to_string e in
                               let uu____10095 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10091 uu____10092 uu____10093
                                 uu____10094 uu____10095))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10136  ->
                match uu____10136 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10180 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____10180, t, c, gvs)) univnames_lecs
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
              (let uu____10227 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____10227 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10233 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10233) in
          let is_var e1 =
            let uu____10240 =
              let uu____10241 = FStar_Syntax_Subst.compress e1 in
              uu____10241.FStar_Syntax_Syntax.n in
            match uu____10240 with
            | FStar_Syntax_Syntax.Tm_name uu____10244 -> true
            | uu____10245 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___172_10261 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___172_10261.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___172_10261.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10262 -> e2 in
          let env2 =
            let uu___173_10264 = env1 in
            let uu____10265 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___173_10264.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___173_10264.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___173_10264.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___173_10264.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___173_10264.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___173_10264.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___173_10264.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___173_10264.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___173_10264.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___173_10264.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___173_10264.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___173_10264.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___173_10264.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___173_10264.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___173_10264.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10265;
              FStar_TypeChecker_Env.is_iface =
                (uu___173_10264.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___173_10264.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___173_10264.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___173_10264.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___173_10264.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___173_10264.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___173_10264.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___173_10264.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___173_10264.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___173_10264.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___173_10264.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___173_10264.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___173_10264.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___173_10264.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___173_10264.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___173_10264.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___173_10264.FStar_TypeChecker_Env.dsenv)
            } in
          let uu____10266 = check env2 t1 t2 in
          match uu____10266 with
          | FStar_Pervasives_Native.None  ->
              let uu____10273 =
                let uu____10274 =
                  let uu____10279 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____10280 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____10279, uu____10280) in
                FStar_Errors.Error uu____10274 in
              FStar_Exn.raise uu____10273
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10287 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10287
                then
                  let uu____10288 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10288
                else ());
               (let uu____10290 = decorate e t2 in (uu____10290, g)))
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
        let uu____10321 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10321
        then
          let uu____10326 = discharge g1 in
          let uu____10327 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10326, uu____10327)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10340 =
               let uu____10341 =
                 let uu____10342 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10342 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10341
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10340
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10344 = destruct_comp c1 in
           match uu____10344 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10361 = FStar_TypeChecker_Env.get_range env in
                 let uu____10362 =
                   let uu____10363 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10364 =
                     let uu____10365 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10366 =
                       let uu____10369 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10369] in
                     uu____10365 :: uu____10366 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10363 uu____10364 in
                 uu____10362 FStar_Pervasives_Native.None uu____10361 in
               ((let uu____10373 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10373
                 then
                   let uu____10374 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10374
                 else ());
                (let g2 =
                   let uu____10377 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10377 in
                 let uu____10378 = discharge g2 in
                 let uu____10379 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10378, uu____10379))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___132_10405 =
        match uu___132_10405 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10413)::[] -> f fst1
        | uu____10430 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10435 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10435
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44) in
      let op_or_e e =
        let uu____10444 =
          let uu____10447 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10447 in
        FStar_All.pipe_right uu____10444
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_or_t t =
        let uu____10458 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10458
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let short_op_ite uu___133_10472 =
        match uu___133_10472 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10480)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10499)::[] ->
            let uu____10528 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10528
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10533 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10543 =
          let uu____10550 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10550) in
        let uu____10555 =
          let uu____10564 =
            let uu____10571 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10571) in
          let uu____10576 =
            let uu____10585 =
              let uu____10592 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10592) in
            let uu____10597 =
              let uu____10606 =
                let uu____10613 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10613) in
              let uu____10618 =
                let uu____10627 =
                  let uu____10634 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10634) in
                [uu____10627; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10606 :: uu____10618 in
            uu____10585 :: uu____10597 in
          uu____10564 :: uu____10576 in
        uu____10543 :: uu____10555 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10685 =
            FStar_Util.find_map table
              (fun uu____10698  ->
                 match uu____10698 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10715 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10715
                     else FStar_Pervasives_Native.None) in
          (match uu____10685 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10718 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10723 =
      let uu____10724 = FStar_Syntax_Util.un_uinst l in
      uu____10724.FStar_Syntax_Syntax.n in
    match uu____10723 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10728 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10754)::uu____10755 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10766 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10773,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10774))::uu____10775 -> bs
      | uu____10792 ->
          let uu____10793 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10793 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10797 =
                 let uu____10798 = FStar_Syntax_Subst.compress t in
                 uu____10798.FStar_Syntax_Syntax.n in
               (match uu____10797 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10802) ->
                    let uu____10819 =
                      FStar_Util.prefix_until
                        (fun uu___134_10859  ->
                           match uu___134_10859 with
                           | (uu____10866,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10867)) ->
                               false
                           | uu____10870 -> true) bs' in
                    (match uu____10819 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10905,uu____10906) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10978,uu____10979) ->
                         let uu____11052 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11070  ->
                                   match uu____11070 with
                                   | (x,uu____11078) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____11052
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11125  ->
                                     match uu____11125 with
                                     | (x,i) ->
                                         let uu____11144 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____11144, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11154 -> bs))
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
          let uu____11195 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____11195
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
        (let uu____11222 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____11222
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11224 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11224))
         else ());
        (let fv =
           let uu____11227 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11227
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
         let uu____11235 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___174_11241 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___174_11241.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___174_11241.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___174_11241.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___174_11241.FStar_Syntax_Syntax.sigattrs)
           }), uu____11235))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___135_11253 =
        match uu___135_11253 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11254 -> false in
      let reducibility uu___136_11258 =
        match uu___136_11258 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11259 -> false in
      let assumption uu___137_11263 =
        match uu___137_11263 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11264 -> false in
      let reification uu___138_11268 =
        match uu___138_11268 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11269 -> true
        | uu____11270 -> false in
      let inferred uu___139_11274 =
        match uu___139_11274 with
        | FStar_Syntax_Syntax.Discriminator uu____11275 -> true
        | FStar_Syntax_Syntax.Projector uu____11276 -> true
        | FStar_Syntax_Syntax.RecordType uu____11281 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11290 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11299 -> false in
      let has_eq uu___140_11303 =
        match uu___140_11303 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11304 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11364 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11369 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11373 =
        let uu____11374 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___141_11378  ->
                  match uu___141_11378 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11379 -> false)) in
        FStar_All.pipe_right uu____11374 Prims.op_Negation in
      if uu____11373
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11392 =
            let uu____11393 =
              let uu____11398 =
                let uu____11399 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11399 msg in
              (uu____11398, r) in
            FStar_Errors.Error uu____11393 in
          FStar_Exn.raise uu____11392 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11407 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11411 =
            let uu____11412 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11412 in
          if uu____11411 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11417),uu____11418) ->
              ((let uu____11434 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11434
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11438 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11438
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11444 ->
              let uu____11453 =
                let uu____11454 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11454 in
              if uu____11453 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11460 ->
              let uu____11467 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11467 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11471 ->
              let uu____11478 =
                let uu____11479 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11479 in
              if uu____11478 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11485 ->
              let uu____11486 =
                let uu____11487 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11487 in
              if uu____11486 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11493 ->
              let uu____11494 =
                let uu____11495 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11495 in
              if uu____11494 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11501 ->
              let uu____11514 =
                let uu____11515 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11515 in
              if uu____11514 then err'1 () else ()
          | uu____11521 -> ()))
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
                          let uu____11594 =
                            let uu____11597 =
                              let uu____11598 =
                                let uu____11605 =
                                  let uu____11606 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11606 in
                                (uu____11605, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11598 in
                            FStar_Syntax_Syntax.mk uu____11597 in
                          uu____11594 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11647  ->
                                  match uu____11647 with
                                  | (x,imp) ->
                                      let uu____11658 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11658, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11660 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11660 in
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
                             let uu____11669 =
                               let uu____11670 =
                                 let uu____11671 =
                                   let uu____11672 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11673 =
                                     let uu____11674 =
                                       let uu____11675 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11675 in
                                     [uu____11674] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11672
                                     uu____11673 in
                                 uu____11671 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11670 in
                             FStar_Syntax_Util.refine x uu____11669 in
                           let uu____11678 =
                             let uu___175_11679 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___175_11679.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___175_11679.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11678) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11694 =
                          FStar_List.map
                            (fun uu____11716  ->
                               match uu____11716 with
                               | (x,uu____11728) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11694 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11777  ->
                                match uu____11777 with
                                | (x,uu____11789) ->
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
                             (let uu____11803 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11803)
                               ||
                               (let uu____11805 =
                                  let uu____11806 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11806.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11805) in
                           let quals =
                             let uu____11810 =
                               let uu____11813 =
                                 let uu____11816 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11816
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11820 =
                                 FStar_List.filter
                                   (fun uu___142_11824  ->
                                      match uu___142_11824 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11825 -> false) iquals in
                               FStar_List.append uu____11813 uu____11820 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11810 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11846 =
                                 let uu____11847 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11847 in
                               FStar_Syntax_Syntax.mk_Total uu____11846 in
                             let uu____11848 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11848 in
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
                           (let uu____11851 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11851
                            then
                              let uu____11852 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11852
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
                                             fun uu____11905  ->
                                               match uu____11905 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11929 =
                                                       let uu____11932 =
                                                         let uu____11933 =
                                                           let uu____11940 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11940,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11933 in
                                                       pos uu____11932 in
                                                     (uu____11929, b)
                                                   else
                                                     (let uu____11944 =
                                                        let uu____11947 =
                                                          let uu____11948 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11948 in
                                                        pos uu____11947 in
                                                      (uu____11944, b)))) in
                                   let pat_true =
                                     let uu____11966 =
                                       let uu____11969 =
                                         let uu____11970 =
                                           let uu____11983 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11983, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11970 in
                                       pos uu____11969 in
                                     (uu____11966,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____12017 =
                                       let uu____12020 =
                                         let uu____12021 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12021 in
                                       pos uu____12020 in
                                     (uu____12017,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____12033 =
                                     let uu____12036 =
                                       let uu____12037 =
                                         let uu____12060 =
                                           let uu____12063 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____12064 =
                                             let uu____12067 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____12067] in
                                           uu____12063 :: uu____12064 in
                                         (arg_exp, uu____12060) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12037 in
                                     FStar_Syntax_Syntax.mk uu____12036 in
                                   uu____12033 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____12074 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____12074
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
                                let uu____12082 =
                                  let uu____12087 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____12087 in
                                let uu____12088 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12082;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12088
                                } in
                              let impl =
                                let uu____12092 =
                                  let uu____12093 =
                                    let uu____12100 =
                                      let uu____12103 =
                                        let uu____12104 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____12104
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____12103] in
                                    ((false, [lb]), uu____12100) in
                                  FStar_Syntax_Syntax.Sig_let uu____12093 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12092;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____12122 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____12122
                               then
                                 let uu____12123 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12123
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
                                fun uu____12165  ->
                                  match uu____12165 with
                                  | (a,uu____12171) ->
                                      let uu____12172 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____12172 with
                                       | (field_name,uu____12178) ->
                                           let field_proj_tm =
                                             let uu____12180 =
                                               let uu____12181 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12181 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12180 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____12198 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12230  ->
                                    match uu____12230 with
                                    | (x,uu____12238) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____12240 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____12240 with
                                         | (field_name,uu____12248) ->
                                             let t =
                                               let uu____12250 =
                                                 let uu____12251 =
                                                   let uu____12254 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12254 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12251 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12250 in
                                             let only_decl =
                                               (let uu____12258 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12258)
                                                 ||
                                                 (let uu____12260 =
                                                    let uu____12261 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____12261.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12260) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12275 =
                                                   FStar_List.filter
                                                     (fun uu___143_12279  ->
                                                        match uu___143_12279
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12280 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12275
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___144_12293  ->
                                                         match uu___144_12293
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12294 ->
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
                                             ((let uu____12313 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12313
                                               then
                                                 let uu____12314 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12314
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
                                                           fun uu____12362 
                                                             ->
                                                             match uu____12362
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12386
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12386,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12402
                                                                    =
                                                                    let uu____12405
                                                                    =
                                                                    let uu____12406
                                                                    =
                                                                    let uu____12413
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12413,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12406 in
                                                                    pos
                                                                    uu____12405 in
                                                                    (uu____12402,
                                                                    b))
                                                                   else
                                                                    (let uu____12417
                                                                    =
                                                                    let uu____12420
                                                                    =
                                                                    let uu____12421
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12421 in
                                                                    pos
                                                                    uu____12420 in
                                                                    (uu____12417,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12437 =
                                                     let uu____12440 =
                                                       let uu____12441 =
                                                         let uu____12454 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12454,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12441 in
                                                     pos uu____12440 in
                                                   let uu____12463 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12437,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12463) in
                                                 let body =
                                                   let uu____12475 =
                                                     let uu____12478 =
                                                       let uu____12479 =
                                                         let uu____12502 =
                                                           let uu____12505 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12505] in
                                                         (arg_exp,
                                                           uu____12502) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12479 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12478 in
                                                   uu____12475
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12513 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12513
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
                                                   let uu____12520 =
                                                     let uu____12525 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12525 in
                                                   let uu____12526 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12520;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12526
                                                   } in
                                                 let impl =
                                                   let uu____12530 =
                                                     let uu____12531 =
                                                       let uu____12538 =
                                                         let uu____12541 =
                                                           let uu____12542 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12542
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12541] in
                                                       ((false, [lb]),
                                                         uu____12538) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12531 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12530;
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
                                                 (let uu____12560 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12560
                                                  then
                                                    let uu____12561 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12561
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____12198 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12605) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12610 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12610 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12632 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12632 with
                    | (formals,uu____12648) ->
                        let uu____12665 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12697 =
                                   let uu____12698 =
                                     let uu____12699 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12699 in
                                   FStar_Ident.lid_equals typ_lid uu____12698 in
                                 if uu____12697
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12718,uvs',tps,typ0,uu____12722,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12741 -> failwith "Impossible"
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
                        (match uu____12665 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12814 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12814 with
                              | (indices,uu____12830) ->
                                  let refine_domain =
                                    let uu____12848 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___145_12853  ->
                                              match uu___145_12853 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12854 -> true
                                              | uu____12863 -> false)) in
                                    if uu____12848
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___146_12871 =
                                      match uu___146_12871 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12874,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12886 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12887 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12887 with
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
                                    let uu____12898 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12898 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12963  ->
                                               fun uu____12964  ->
                                                 match (uu____12963,
                                                         uu____12964)
                                                 with
                                                 | ((x,uu____12982),(x',uu____12984))
                                                     ->
                                                     let uu____12993 =
                                                       let uu____13000 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____13000) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12993) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13001 -> []