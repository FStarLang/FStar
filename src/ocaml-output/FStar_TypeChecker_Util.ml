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
            let uu____4354 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Parser_Const.effect_GTot_lid in
            FStar_All.pipe_left Prims.op_Negation uu____4354 in
          if uu____4353
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               FStar_TypeChecker_Env.get_effect_decl env
                 FStar_Parser_Const.effect_PURE_lid in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t in
             let wp =
               let uu____4359 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
               if uu____4359
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____4361 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Parser_Const.effect_PURE_lid in
                  match uu____4361 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp in
                      let uu____4369 =
                        let uu____4370 =
                          let uu____4371 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp in
                          let uu____4372 =
                            let uu____4373 = FStar_Syntax_Syntax.as_arg t in
                            let uu____4374 =
                              let uu____4377 = FStar_Syntax_Syntax.as_arg v1 in
                              [uu____4377] in
                            uu____4373 :: uu____4374 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____4371 uu____4372 in
                        uu____4370 FStar_Pervasives_Native.None
                          v1.FStar_Syntax_Syntax.pos in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.NoFullNorm] env
                        uu____4369) in
             mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]) in
        (let uu____4381 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return") in
         if uu____4381
         then
           let uu____4382 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos in
           let uu____4383 = FStar_Syntax_Print.term_to_string v1 in
           let uu____4384 = FStar_TypeChecker_Normalize.comp_to_string env c in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____4382
             uu____4383 uu____4384
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
          fun uu____4407  ->
            match uu____4407 with
            | (b,lc2) ->
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1 in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2 in
                let joined_eff = join_lcomp env lc11 lc21 in
                ((let uu____4420 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind")) in
                  if uu____4420
                  then
                    let bstr =
                      match b with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_Syntax_Print.bv_to_string x in
                    let uu____4423 =
                      match e1opt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some e ->
                          FStar_Syntax_Print.term_to_string e in
                    let uu____4425 = FStar_Syntax_Print.lcomp_to_string lc11 in
                    let uu____4426 = FStar_Syntax_Print.lcomp_to_string lc21 in
                    FStar_Util.print4
                      "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                      uu____4423 uu____4425 bstr uu____4426
                  else ());
                 (let bind_it uu____4431 =
                    let uu____4432 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ()) in
                    if uu____4432
                    then
                      let u_t =
                        env.FStar_TypeChecker_Env.universe_of env
                          lc21.FStar_Syntax_Syntax.res_typ in
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_Syntax_Syntax.res_typ []
                    else
                      (let c1 = lc11.FStar_Syntax_Syntax.comp () in
                       let c2 = lc21.FStar_Syntax_Syntax.comp () in
                       (let uu____4442 =
                          (FStar_TypeChecker_Env.debug env
                             FStar_Options.Extreme)
                            ||
                            (FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "bind")) in
                        if uu____4442
                        then
                          let uu____4443 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x in
                          let uu____4445 =
                            FStar_Syntax_Print.lcomp_to_string lc11 in
                          let uu____4446 =
                            FStar_Syntax_Print.comp_to_string c1 in
                          let uu____4447 =
                            FStar_Syntax_Print.lcomp_to_string lc21 in
                          let uu____4448 =
                            FStar_Syntax_Print.comp_to_string c2 in
                          FStar_Util.print5
                            "b=%s,Evaluated %s to %s\n And %s to %s\n"
                            uu____4443 uu____4445 uu____4446 uu____4447
                            uu____4448
                        else ());
                       (let try_simplify uu____4463 =
                          let aux uu____4477 =
                            let uu____4478 =
                              FStar_Syntax_Util.is_trivial_wp c1 in
                            if uu____4478
                            then
                              match b with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Util.Inl (c2, "trivial no binder")
                              | FStar_Pervasives_Native.Some uu____4507 ->
                                  let uu____4508 =
                                    FStar_Syntax_Util.is_ml_comp c2 in
                                  (if uu____4508
                                   then FStar_Util.Inl (c2, "trivial ml")
                                   else
                                     FStar_Util.Inr
                                       "c1 trivial; but c2 is not ML")
                            else
                              (let uu____4535 =
                                 (FStar_Syntax_Util.is_ml_comp c1) &&
                                   (FStar_Syntax_Util.is_ml_comp c2) in
                               if uu____4535
                               then FStar_Util.Inl (c2, "both ml")
                               else
                                 FStar_Util.Inr
                                   "c1 not trivial, and both are not ML") in
                          let subst_c2 reason =
                            match (e1opt, b) with
                            | (FStar_Pervasives_Native.Some
                               e,FStar_Pervasives_Native.Some x) ->
                                let uu____4591 =
                                  let uu____4596 =
                                    FStar_Syntax_Subst.subst_comp
                                      [FStar_Syntax_Syntax.NT (x, e)] c2 in
                                  (uu____4596, reason) in
                                FStar_Util.Inl uu____4591
                            | uu____4601 -> aux () in
                          let rec maybe_close t x c =
                            let uu____4620 =
                              let uu____4621 =
                                FStar_TypeChecker_Normalize.unfold_whnf env t in
                              uu____4621.FStar_Syntax_Syntax.n in
                            match uu____4620 with
                            | FStar_Syntax_Syntax.Tm_refine (y,uu____4625) ->
                                maybe_close y.FStar_Syntax_Syntax.sort x c
                            | FStar_Syntax_Syntax.Tm_fvar fv when
                                FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.unit_lid
                                -> close_comp env [x] c
                            | uu____4631 -> c in
                          let uu____4632 =
                            let uu____4633 =
                              FStar_TypeChecker_Env.try_lookup_effect_lid env
                                FStar_Parser_Const.effect_GTot_lid in
                            FStar_Option.isNone uu____4633 in
                          if uu____4632
                          then
                            let uu____4646 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                            (if uu____4646
                             then
                               FStar_Util.Inl
                                 (c2,
                                   "Early in prims; we don't have bind yet")
                             else
                               (let uu____4666 =
                                  let uu____4667 =
                                    let uu____4672 =
                                      FStar_TypeChecker_Env.get_range env in
                                    ("Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad",
                                      uu____4672) in
                                  FStar_Errors.Error uu____4667 in
                                FStar_Exn.raise uu____4666))
                          else
                            (let uu____4684 =
                               (FStar_Syntax_Util.is_total_comp c1) &&
                                 (FStar_Syntax_Util.is_total_comp c2) in
                             if uu____4684
                             then subst_c2 "both total"
                             else
                               (let uu____4696 =
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
                                    &&
                                    (FStar_Syntax_Util.is_tot_or_gtot_comp c2) in
                                if uu____4696
                                then
                                  let uu____4707 =
                                    let uu____4712 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Util.comp_result c2) in
                                    (uu____4712, "both gtot") in
                                  FStar_Util.Inl uu____4707
                                else
                                  (match (e1opt, b) with
                                   | (FStar_Pervasives_Native.Some
                                      e,FStar_Pervasives_Native.Some x) ->
                                       let uu____4738 =
                                         (FStar_Syntax_Util.is_total_comp c1)
                                           &&
                                           (let uu____4740 =
                                              FStar_Syntax_Syntax.is_null_bv
                                                x in
                                            Prims.op_Negation uu____4740) in
                                       if uu____4738
                                       then
                                         let c21 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.NT (x, e)]
                                             c2 in
                                         let x1 =
                                           let uu___158_4753 = x in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___158_4753.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___158_4753.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           } in
                                         let uu____4754 =
                                           let uu____4759 =
                                             maybe_close
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c21 in
                                           (uu____4759, "c1 Tot") in
                                         FStar_Util.Inl uu____4754
                                       else aux ()
                                   | uu____4765 -> aux ()))) in
                        let uu____4774 = try_simplify () in
                        match uu____4774 with
                        | FStar_Util.Inl (c,reason) ->
                            ((let uu____4798 =
                                (FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme)
                                  ||
                                  (FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "bind")) in
                              if uu____4798
                              then
                                let uu____4799 =
                                  FStar_Syntax_Print.comp_to_string c1 in
                                let uu____4800 =
                                  FStar_Syntax_Print.comp_to_string c2 in
                                let uu____4801 =
                                  FStar_Syntax_Print.comp_to_string c in
                                FStar_Util.print4
                                  "Simplified (because %s) bind %s %s to %s\n"
                                  reason uu____4799 uu____4800 uu____4801
                              else ());
                             c)
                        | FStar_Util.Inr reason ->
                            let uu____4810 = lift_and_destruct env c1 c2 in
                            (match uu____4810 with
                             | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                 let bs =
                                   match b with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4867 =
                                         FStar_Syntax_Syntax.null_binder t1 in
                                       [uu____4867]
                                   | FStar_Pervasives_Native.Some x ->
                                       let uu____4869 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____4869] in
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
                                   let uu____4882 =
                                     FStar_Syntax_Syntax.as_arg r11 in
                                   let uu____4883 =
                                     let uu____4886 =
                                       FStar_Syntax_Syntax.as_arg t1 in
                                     let uu____4887 =
                                       let uu____4890 =
                                         FStar_Syntax_Syntax.as_arg t2 in
                                       let uu____4891 =
                                         let uu____4894 =
                                           FStar_Syntax_Syntax.as_arg wp1 in
                                         let uu____4895 =
                                           let uu____4898 =
                                             let uu____4899 = mk_lam wp2 in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____4899 in
                                           [uu____4898] in
                                         uu____4894 :: uu____4895 in
                                       uu____4890 :: uu____4891 in
                                     uu____4886 :: uu____4887 in
                                   uu____4882 :: uu____4883 in
                                 let k =
                                   FStar_Syntax_Subst.subst
                                     [FStar_Syntax_Syntax.NT (a, t2)] kwp in
                                 let wp =
                                   let uu____4904 =
                                     let uu____4905 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_t1; u_t2] env md
                                         md.FStar_Syntax_Syntax.bind_wp in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____4905
                                       wp_args in
                                   uu____4904 FStar_Pervasives_Native.None
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
              let uu____4952 =
                let uu____4953 = FStar_TypeChecker_Env.should_verify env in
                FStar_All.pipe_left Prims.op_Negation uu____4953 in
              if uu____4952
              then f
              else (let uu____4955 = reason1 () in label uu____4955 r f)
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
            let uu___159_4969 = g in
            let uu____4970 =
              let uu____4971 = label reason r f in
              FStar_TypeChecker_Common.NonTrivial uu____4971 in
            {
              FStar_TypeChecker_Env.guard_f = uu____4970;
              FStar_TypeChecker_Env.deferred =
                (uu___159_4969.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___159_4969.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___159_4969.FStar_TypeChecker_Env.implicits)
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
      | uu____4983 -> g2
let weaken_precondition:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5005 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5009 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5009
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 ->
                 let uu____5016 = FStar_Syntax_Util.is_ml_comp c in
                 if uu____5016
                 then c
                 else
                   (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                    let uu____5021 = destruct_comp c1 in
                    match uu____5021 with
                    | (u_res_t,res_t,wp) ->
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c1.FStar_Syntax_Syntax.effect_name in
                        let wp1 =
                          let uu____5037 =
                            let uu____5038 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [u_res_t] env md
                                md.FStar_Syntax_Syntax.assume_p in
                            let uu____5039 =
                              let uu____5040 =
                                FStar_Syntax_Syntax.as_arg res_t in
                              let uu____5041 =
                                let uu____5044 =
                                  FStar_Syntax_Syntax.as_arg f1 in
                                let uu____5045 =
                                  let uu____5048 =
                                    FStar_Syntax_Syntax.as_arg wp in
                                  [uu____5048] in
                                uu____5044 :: uu____5045 in
                              uu____5040 :: uu____5041 in
                            FStar_Syntax_Syntax.mk_Tm_app uu____5038
                              uu____5039 in
                          uu____5037 FStar_Pervasives_Native.None
                            wp.FStar_Syntax_Syntax.pos in
                        mk_comp md u_res_t res_t wp1
                          c1.FStar_Syntax_Syntax.flags)) in
        let uu___160_5051 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___160_5051.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___160_5051.FStar_Syntax_Syntax.res_typ);
          FStar_Syntax_Syntax.cflags =
            (uu___160_5051.FStar_Syntax_Syntax.cflags);
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
            let uu____5089 = FStar_TypeChecker_Rel.is_trivial g0 in
            if uu____5089
            then (lc, g0)
            else
              ((let uu____5096 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme in
                if uu____5096
                then
                  let uu____5097 =
                    FStar_TypeChecker_Normalize.term_to_string env e in
                  let uu____5098 =
                    FStar_TypeChecker_Rel.guard_to_string env g0 in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____5097 uu____5098
                else ());
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                    (FStar_List.collect
                       (fun uu___129_5108  ->
                          match uu___129_5108 with
                          | FStar_Syntax_Syntax.RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____5111 -> [])) in
                let strengthen uu____5117 =
                  let c = lc.FStar_Syntax_Syntax.comp () in
                  if env.FStar_TypeChecker_Env.lax
                  then c
                  else
                    (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0 in
                     let uu____5125 = FStar_TypeChecker_Rel.guard_form g01 in
                     match uu____5125 with
                     | FStar_TypeChecker_Common.Trivial  -> c
                     | FStar_TypeChecker_Common.NonTrivial f ->
                         let c1 =
                           let uu____5132 =
                             (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                               (let uu____5134 =
                                  FStar_Syntax_Util.is_partial_return c in
                                Prims.op_Negation uu____5134) in
                           if uu____5132
                           then
                             let x =
                               FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                                 FStar_Pervasives_Native.None
                                 (FStar_Syntax_Util.comp_result c) in
                             let xret =
                               let uu____5141 =
                                 let uu____5142 =
                                   FStar_Syntax_Syntax.bv_to_name x in
                                 return_value env x.FStar_Syntax_Syntax.sort
                                   uu____5142 in
                               FStar_Syntax_Util.comp_set_flags uu____5141
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                             let lc1 =
                               bind e.FStar_Syntax_Syntax.pos env
                                 (FStar_Pervasives_Native.Some e)
                                 (FStar_Syntax_Util.lcomp_of_comp c)
                                 ((FStar_Pervasives_Native.Some x),
                                   (FStar_Syntax_Util.lcomp_of_comp xret)) in
                             lc1.FStar_Syntax_Syntax.comp ()
                           else c in
                         ((let uu____5148 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               FStar_Options.Extreme in
                           if uu____5148
                           then
                             let uu____5149 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 e in
                             let uu____5150 =
                               FStar_TypeChecker_Normalize.term_to_string env
                                 f in
                             FStar_Util.print2
                               "-------------Strengthening pre-condition of term %s with guard %s\n"
                               uu____5149 uu____5150
                           else ());
                          (let c2 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c1 in
                           let uu____5153 = destruct_comp c2 in
                           match uu____5153 with
                           | (u_res_t,res_t,wp) ->
                               let md =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   c2.FStar_Syntax_Syntax.effect_name in
                               let wp1 =
                                 let uu____5169 =
                                   let uu____5170 =
                                     FStar_TypeChecker_Env.inst_effect_fun_with
                                       [u_res_t] env md
                                       md.FStar_Syntax_Syntax.assert_p in
                                   let uu____5171 =
                                     let uu____5172 =
                                       FStar_Syntax_Syntax.as_arg res_t in
                                     let uu____5173 =
                                       let uu____5176 =
                                         let uu____5177 =
                                           let uu____5178 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           label_opt env reason uu____5178 f in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5177 in
                                       let uu____5179 =
                                         let uu____5182 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [uu____5182] in
                                       uu____5176 :: uu____5179 in
                                     uu____5172 :: uu____5173 in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____5170
                                     uu____5171 in
                                 uu____5169 FStar_Pervasives_Native.None
                                   wp.FStar_Syntax_Syntax.pos in
                               ((let uu____5186 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme in
                                 if uu____5186
                                 then
                                   let uu____5187 =
                                     FStar_Syntax_Print.term_to_string wp1 in
                                   FStar_Util.print1
                                     "-------------Strengthened pre-condition is %s\n"
                                     uu____5187
                                 else ());
                                (let c21 = mk_comp md u_res_t res_t wp1 flags in
                                 c21))))) in
                let uu____5190 =
                  let uu___161_5191 = lc in
                  let uu____5192 =
                    FStar_TypeChecker_Env.norm_eff_name env
                      lc.FStar_Syntax_Syntax.eff_name in
                  let uu____5193 =
                    let uu____5196 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____5198 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.res_typ in
                         FStar_All.pipe_left Prims.op_Negation uu____5198) in
                    if uu____5196 then flags else [] in
                  {
                    FStar_Syntax_Syntax.eff_name = uu____5192;
                    FStar_Syntax_Syntax.res_typ =
                      (uu___161_5191.FStar_Syntax_Syntax.res_typ);
                    FStar_Syntax_Syntax.cflags = uu____5193;
                    FStar_Syntax_Syntax.comp = strengthen
                  } in
                (uu____5190,
                  (let uu___162_5203 = g0 in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___162_5203.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___162_5203.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___162_5203.FStar_TypeChecker_Env.implicits)
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
        let uu____5221 =
          let uu____5226 = FStar_Syntax_Syntax.bv_to_name x in
          let uu____5227 = FStar_Syntax_Syntax.bv_to_name y in
          (uu____5226, uu____5227) in
        match uu____5221 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
            let yret =
              let uu____5236 =
                let uu____5237 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp in
                let uu____5238 =
                  let uu____5239 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5240 =
                    let uu____5243 = FStar_Syntax_Syntax.as_arg yexp in
                    [uu____5243] in
                  uu____5239 :: uu____5240 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5237 uu____5238 in
              uu____5236 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let x_eq_y_yret =
              let uu____5249 =
                let uu____5250 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p in
                let uu____5251 =
                  let uu____5252 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5253 =
                    let uu____5256 =
                      let uu____5257 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____5257 in
                    let uu____5258 =
                      let uu____5261 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret in
                      [uu____5261] in
                    uu____5256 :: uu____5258 in
                  uu____5252 :: uu____5253 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5250 uu____5251 in
              uu____5249 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let forall_y_x_eq_y_yret =
              let uu____5267 =
                let uu____5268 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp in
                let uu____5269 =
                  let uu____5270 = FStar_Syntax_Syntax.as_arg res_t in
                  let uu____5271 =
                    let uu____5274 = FStar_Syntax_Syntax.as_arg res_t in
                    let uu____5275 =
                      let uu____5278 =
                        let uu____5279 =
                          let uu____5280 =
                            let uu____5281 = FStar_Syntax_Syntax.mk_binder y in
                            [uu____5281] in
                          FStar_Syntax_Util.abs uu____5280 x_eq_y_yret
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.mk_residual_comp
                                  FStar_Parser_Const.effect_Tot_lid
                                  FStar_Pervasives_Native.None
                                  [FStar_Syntax_Syntax.TOTAL])) in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____5279 in
                      [uu____5278] in
                    uu____5274 :: uu____5275 in
                  uu____5270 :: uu____5271 in
                FStar_Syntax_Syntax.mk_Tm_app uu____5268 uu____5269 in
              uu____5267 FStar_Pervasives_Native.None
                res_t.FStar_Syntax_Syntax.pos in
            let lc2 =
              mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN] in
            let lc =
              let uu____5288 = FStar_TypeChecker_Env.get_range env in
              bind uu____5288 env FStar_Pervasives_Native.None
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
          let comp uu____5311 =
            let uu____5312 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
            if uu____5312
            then
              let u_t =
                env.FStar_TypeChecker_Env.universe_of env
                  lcomp_then.FStar_Syntax_Syntax.res_typ in
              lax_mk_tot_or_comp_l joined_eff u_t
                lcomp_then.FStar_Syntax_Syntax.res_typ []
            else
              (let uu____5315 =
                 let uu____5340 = lcomp_then.FStar_Syntax_Syntax.comp () in
                 let uu____5341 = lcomp_else.FStar_Syntax_Syntax.comp () in
                 lift_and_destruct env uu____5340 uu____5341 in
               match uu____5315 with
               | ((md,uu____5343,uu____5344),(u_res_t,res_t,wp_then),
                  (uu____5348,uu____5349,wp_else)) ->
                   let ifthenelse md1 res_t1 g wp_t wp_e =
                     let uu____5387 =
                       FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                         wp_e.FStar_Syntax_Syntax.pos in
                     let uu____5388 =
                       let uu____5389 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md1 md1.FStar_Syntax_Syntax.if_then_else in
                       let uu____5390 =
                         let uu____5391 = FStar_Syntax_Syntax.as_arg res_t1 in
                         let uu____5392 =
                           let uu____5395 = FStar_Syntax_Syntax.as_arg g in
                           let uu____5396 =
                             let uu____5399 = FStar_Syntax_Syntax.as_arg wp_t in
                             let uu____5400 =
                               let uu____5403 =
                                 FStar_Syntax_Syntax.as_arg wp_e in
                               [uu____5403] in
                             uu____5399 :: uu____5400 in
                           uu____5395 :: uu____5396 in
                         uu____5391 :: uu____5392 in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5389 uu____5390 in
                     uu____5388 FStar_Pervasives_Native.None uu____5387 in
                   let wp = ifthenelse md res_t guard wp_then wp_else in
                   let uu____5409 =
                     let uu____5410 = FStar_Options.split_cases () in
                     uu____5410 > (Prims.parse_int "0") in
                   if uu____5409
                   then
                     let comp = mk_comp md u_res_t res_t wp [] in
                     add_equality_to_post_condition env comp res_t
                   else
                     (let wp1 =
                        let uu____5416 =
                          let uu____5417 =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                          let uu____5418 =
                            let uu____5419 = FStar_Syntax_Syntax.as_arg res_t in
                            let uu____5420 =
                              let uu____5423 = FStar_Syntax_Syntax.as_arg wp in
                              [uu____5423] in
                            uu____5419 :: uu____5420 in
                          FStar_Syntax_Syntax.mk_Tm_app uu____5417 uu____5418 in
                        uu____5416 FStar_Pervasives_Native.None
                          wp.FStar_Syntax_Syntax.pos in
                      mk_comp md u_res_t res_t wp1 [])) in
          let uu____5426 =
            join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name
              lcomp_else.FStar_Syntax_Syntax.eff_name in
          {
            FStar_Syntax_Syntax.eff_name = uu____5426;
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
      let uu____5435 =
        let uu____5436 = FStar_TypeChecker_Env.get_range env in
        FStar_Ident.set_lid_range lid uu____5436 in
      FStar_Syntax_Syntax.fvar uu____5435 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____5471  ->
                 match uu____5471 with
                 | (uu____5476,lc) ->
                     join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
            FStar_Parser_Const.effect_PURE_lid lcases in
        let bind_cases uu____5481 =
          let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t in
          let uu____5483 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()) in
          if uu____5483
          then lax_mk_tot_or_comp_l eff u_res_t res_t []
          else
            (let ifthenelse md res_t1 g wp_t wp_e =
               let uu____5503 =
                 FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                   wp_e.FStar_Syntax_Syntax.pos in
               let uu____5504 =
                 let uu____5505 =
                   FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                     md md.FStar_Syntax_Syntax.if_then_else in
                 let uu____5506 =
                   let uu____5507 = FStar_Syntax_Syntax.as_arg res_t1 in
                   let uu____5508 =
                     let uu____5511 = FStar_Syntax_Syntax.as_arg g in
                     let uu____5512 =
                       let uu____5515 = FStar_Syntax_Syntax.as_arg wp_t in
                       let uu____5516 =
                         let uu____5519 = FStar_Syntax_Syntax.as_arg wp_e in
                         [uu____5519] in
                       uu____5515 :: uu____5516 in
                     uu____5511 :: uu____5512 in
                   uu____5507 :: uu____5508 in
                 FStar_Syntax_Syntax.mk_Tm_app uu____5505 uu____5506 in
               uu____5504 FStar_Pervasives_Native.None uu____5503 in
             let default_case =
               let post_k =
                 let uu____5526 =
                   let uu____5533 = FStar_Syntax_Syntax.null_binder res_t in
                   [uu____5533] in
                 let uu____5534 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5526 uu____5534 in
               let kwp =
                 let uu____5540 =
                   let uu____5547 = FStar_Syntax_Syntax.null_binder post_k in
                   [uu____5547] in
                 let uu____5548 =
                   FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                 FStar_Syntax_Util.arrow uu____5540 uu____5548 in
               let post =
                 FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                   post_k in
               let wp =
                 let uu____5553 =
                   let uu____5554 = FStar_Syntax_Syntax.mk_binder post in
                   [uu____5554] in
                 let uu____5555 =
                   let uu____5556 =
                     let uu____5559 = FStar_TypeChecker_Env.get_range env in
                     label FStar_TypeChecker_Err.exhaustiveness_check
                       uu____5559 in
                   let uu____5560 =
                     fvar_const env FStar_Parser_Const.false_lid in
                   FStar_All.pipe_left uu____5556 uu____5560 in
                 FStar_Syntax_Util.abs uu____5553 uu____5555
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
                 (fun uu____5584  ->
                    fun celse  ->
                      match uu____5584 with
                      | (g,cthen) ->
                          let uu____5592 =
                            let uu____5617 =
                              cthen.FStar_Syntax_Syntax.comp () in
                            lift_and_destruct env uu____5617 celse in
                          (match uu____5592 with
                           | ((md,uu____5619,uu____5620),(uu____5621,uu____5622,wp_then),
                              (uu____5624,uu____5625,wp_else)) ->
                               let uu____5645 =
                                 ifthenelse md res_t g wp_then wp_else in
                               mk_comp md u_res_t res_t uu____5645 []))
                 lcases default_case in
             let uu____5646 =
               let uu____5647 = FStar_Options.split_cases () in
               uu____5647 > (Prims.parse_int "0") in
             if uu____5646
             then add_equality_to_post_condition env comp res_t
             else
               (let comp1 = FStar_TypeChecker_Env.comp_to_comp_typ env comp in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    comp1.FStar_Syntax_Syntax.effect_name in
                let uu____5651 = destruct_comp comp1 in
                match uu____5651 with
                | (uu____5658,uu____5659,wp) ->
                    let wp1 =
                      let uu____5664 =
                        let uu____5665 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_res_t] env md md.FStar_Syntax_Syntax.ite_wp in
                        let uu____5666 =
                          let uu____5667 = FStar_Syntax_Syntax.as_arg res_t in
                          let uu____5668 =
                            let uu____5671 = FStar_Syntax_Syntax.as_arg wp in
                            [uu____5671] in
                          uu____5667 :: uu____5668 in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5665 uu____5666 in
                      uu____5664 FStar_Pervasives_Native.None
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
          let uu____5689 =
            ((let uu____5692 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.res_typ in
              Prims.op_Negation uu____5692) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____5694 = FStar_Syntax_Util.is_lcomp_partial_return lc in
               Prims.op_Negation uu____5694) in
          if uu____5689
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.cflags)
          else lc.FStar_Syntax_Syntax.cflags in
        let refine1 uu____5703 =
          let c = lc.FStar_Syntax_Syntax.comp () in
          let uu____5707 =
            (let uu____5710 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name in
             Prims.op_Negation uu____5710) || env.FStar_TypeChecker_Env.lax in
          if uu____5707
          then c
          else
            (let uu____5714 = FStar_Syntax_Util.is_partial_return c in
             if uu____5714
             then c
             else
               (let uu____5718 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                if uu____5718
                then
                  let uu____5721 =
                    let uu____5722 =
                      FStar_TypeChecker_Env.lid_exists env
                        FStar_Parser_Const.effect_GTot_lid in
                    Prims.op_Negation uu____5722 in
                  (if uu____5721
                   then
                     let uu____5725 =
                       let uu____5726 =
                         FStar_Range.string_of_range
                           e.FStar_Syntax_Syntax.pos in
                       let uu____5727 = FStar_Syntax_Print.term_to_string e in
                       FStar_Util.format2 "%s: %s\n" uu____5726 uu____5727 in
                     failwith uu____5725
                   else
                     (let retc =
                        return_value env (FStar_Syntax_Util.comp_result c) e in
                      let uu____5732 =
                        let uu____5733 = FStar_Syntax_Util.is_pure_comp c in
                        Prims.op_Negation uu____5733 in
                      if uu____5732
                      then
                        let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc in
                        let retc2 =
                          let uu___163_5738 = retc1 in
                          {
                            FStar_Syntax_Syntax.comp_univs =
                              (uu___163_5738.FStar_Syntax_Syntax.comp_univs);
                            FStar_Syntax_Syntax.effect_name =
                              FStar_Parser_Const.effect_GHOST_lid;
                            FStar_Syntax_Syntax.result_typ =
                              (uu___163_5738.FStar_Syntax_Syntax.result_typ);
                            FStar_Syntax_Syntax.effect_args =
                              (uu___163_5738.FStar_Syntax_Syntax.effect_args);
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
                     let uu____5749 =
                       let uu____5752 = return_value env t xexp in
                       FStar_Syntax_Util.comp_set_flags uu____5752
                         [FStar_Syntax_Syntax.PARTIAL_RETURN] in
                     FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                       uu____5749 in
                   let eq1 =
                     let uu____5756 =
                       env.FStar_TypeChecker_Env.universe_of env t in
                     FStar_Syntax_Util.mk_eq2 uu____5756 t xexp e in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1) in
                   let uu____5758 =
                     let uu____5759 =
                       let uu____5764 =
                         bind e.FStar_Syntax_Syntax.pos env
                           FStar_Pervasives_Native.None
                           (FStar_Syntax_Util.lcomp_of_comp c2)
                           ((FStar_Pervasives_Native.Some x), eq_ret) in
                       uu____5764.FStar_Syntax_Syntax.comp in
                     uu____5759 () in
                   FStar_Syntax_Util.comp_set_flags uu____5758 flags))) in
        let uu___164_5767 = lc in
        {
          FStar_Syntax_Syntax.eff_name =
            (uu___164_5767.FStar_Syntax_Syntax.eff_name);
          FStar_Syntax_Syntax.res_typ =
            (uu___164_5767.FStar_Syntax_Syntax.res_typ);
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
          let uu____5796 = FStar_TypeChecker_Rel.sub_comp env c c' in
          match uu____5796 with
          | FStar_Pervasives_Native.None  ->
              let uu____5805 =
                let uu____5806 =
                  let uu____5811 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c' in
                  let uu____5812 = FStar_TypeChecker_Env.get_range env in
                  (uu____5811, uu____5812) in
                FStar_Errors.Error uu____5806 in
              FStar_Exn.raise uu____5805
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
            let uu____5849 =
              let uu____5850 = FStar_Syntax_Subst.compress t2 in
              uu____5850.FStar_Syntax_Syntax.n in
            match uu____5849 with
            | FStar_Syntax_Syntax.Tm_type uu____5853 -> true
            | uu____5854 -> false in
          let uu____5855 =
            let uu____5856 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ in
            uu____5856.FStar_Syntax_Syntax.n in
          match uu____5855 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____5864 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None in
              let lc1 =
                let uu____5875 =
                  let uu____5876 =
                    let uu____5877 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____5877 in
                  (FStar_Pervasives_Native.None, uu____5876) in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____5875 in
              let e1 =
                let uu____5887 =
                  let uu____5888 =
                    let uu____5889 = FStar_Syntax_Syntax.as_arg e in
                    [uu____5889] in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5888 in
                uu____5887 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
              (e1, lc1)
          | uu____5894 -> (e, lc)
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
              (let uu____5927 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name in
               match uu____5927 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____5950 -> false) in
          let gopt =
            if use_eq
            then
              let uu____5972 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t in
              (uu____5972, false)
            else
              (let uu____5978 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.res_typ t in
               (uu____5978, true)) in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____5989) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____5998 =
                  let uu____5999 =
                    let uu____6004 =
                      FStar_TypeChecker_Err.basic_type_error env
                        (FStar_Pervasives_Native.Some e) t
                        lc.FStar_Syntax_Syntax.res_typ in
                    (uu____6004, (e.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____5999 in
                FStar_Exn.raise uu____5998
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___165_6014 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___165_6014.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___165_6014.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___165_6014.FStar_Syntax_Syntax.comp)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6019 = FStar_TypeChecker_Rel.guard_form g in
              (match uu____6019 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___166_6027 = lc in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___166_6027.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___166_6027.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp =
                         (uu___166_6027.FStar_Syntax_Syntax.comp)
                     } in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___167_6030 = g in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___167_6030.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___167_6030.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___167_6030.FStar_TypeChecker_Env.implicits)
                     } in
                   let strengthen uu____6036 =
                     let uu____6037 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ()) in
                     if uu____6037
                     then lc.FStar_Syntax_Syntax.comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f in
                        let uu____6042 =
                          let uu____6043 = FStar_Syntax_Subst.compress f1 in
                          uu____6043.FStar_Syntax_Syntax.n in
                        match uu____6042 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6048,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6050;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6051;_},uu____6052)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___168_6074 = lc in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___168_6074.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___168_6074.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp =
                                  (uu___168_6074.FStar_Syntax_Syntax.comp)
                              } in
                            lc1.FStar_Syntax_Syntax.comp ()
                        | uu____6075 ->
                            let c = lc.FStar_Syntax_Syntax.comp () in
                            ((let uu____6080 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme in
                              if uu____6080
                              then
                                let uu____6081 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ in
                                let uu____6082 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t in
                                let uu____6083 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c in
                                let uu____6084 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1 in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6081 uu____6082 uu____6083 uu____6084
                              else ());
                             (let ct =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c in
                              let uu____6087 =
                                FStar_TypeChecker_Env.wp_signature env
                                  FStar_Parser_Const.effect_PURE_lid in
                              match uu____6087 with
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
                                  let uu____6100 = destruct_comp ct in
                                  (match uu____6100 with
                                   | (u_t,uu____6110,uu____6111) ->
                                       let wp =
                                         let uu____6115 =
                                           let uu____6116 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u_t] env md
                                               md.FStar_Syntax_Syntax.ret_wp in
                                           let uu____6117 =
                                             let uu____6118 =
                                               FStar_Syntax_Syntax.as_arg t in
                                             let uu____6119 =
                                               let uu____6122 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6122] in
                                             uu____6118 :: uu____6119 in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6116 uu____6117 in
                                         uu____6115
                                           FStar_Pervasives_Native.None
                                           xexp.FStar_Syntax_Syntax.pos in
                                       let cret =
                                         let uu____6126 =
                                           mk_comp md u_t t wp
                                             [FStar_Syntax_Syntax.RETURN] in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.lcomp_of_comp
                                           uu____6126 in
                                       let guard =
                                         if apply_guard1
                                         then
                                           let uu____6136 =
                                             let uu____6137 =
                                               let uu____6138 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   xexp in
                                               [uu____6138] in
                                             FStar_Syntax_Syntax.mk_Tm_app f1
                                               uu____6137 in
                                           uu____6136
                                             FStar_Pervasives_Native.None
                                             f1.FStar_Syntax_Syntax.pos
                                         else f1 in
                                       let uu____6142 =
                                         let uu____6147 =
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41)
                                             (FStar_TypeChecker_Err.subtyping_failed
                                                env
                                                lc.FStar_Syntax_Syntax.res_typ
                                                t) in
                                         let uu____6160 =
                                           FStar_TypeChecker_Env.set_range
                                             env e.FStar_Syntax_Syntax.pos in
                                         let uu____6161 =
                                           FStar_All.pipe_left
                                             FStar_TypeChecker_Rel.guard_of_guard_formula
                                             (FStar_TypeChecker_Common.NonTrivial
                                                guard) in
                                         strengthen_precondition uu____6147
                                           uu____6160 e cret uu____6161 in
                                       (match uu____6142 with
                                        | (eq_ret,_trivial_so_ok_to_discard)
                                            ->
                                            let x1 =
                                              let uu___169_6167 = x in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___169_6167.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___169_6167.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (lc.FStar_Syntax_Syntax.res_typ)
                                              } in
                                            let c1 =
                                              let uu____6169 =
                                                let uu____6170 =
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    ct in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Util.lcomp_of_comp
                                                  uu____6170 in
                                              bind e.FStar_Syntax_Syntax.pos
                                                env
                                                (FStar_Pervasives_Native.Some
                                                   e) uu____6169
                                                ((FStar_Pervasives_Native.Some
                                                    x1), eq_ret) in
                                            let c2 =
                                              c1.FStar_Syntax_Syntax.comp () in
                                            ((let uu____6181 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  FStar_Options.Extreme in
                                              if uu____6181
                                              then
                                                let uu____6182 =
                                                  FStar_TypeChecker_Normalize.comp_to_string
                                                    env c2 in
                                                FStar_Util.print1
                                                  "Strengthened to %s\n"
                                                  uu____6182
                                              else ());
                                             c2)))))) in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___130_6192  ->
                             match uu___130_6192 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6195 -> [])) in
                   let lc1 =
                     let uu___170_6197 = lc in
                     let uu____6198 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name in
                     {
                       FStar_Syntax_Syntax.eff_name = uu____6198;
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags = flags;
                       FStar_Syntax_Syntax.comp = strengthen
                     } in
                   let g2 =
                     let uu___171_6200 = g1 in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___171_6200.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___171_6200.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___171_6200.FStar_TypeChecker_Env.implicits)
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
        let uu____6225 =
          let uu____6226 =
            let uu____6227 =
              let uu____6228 =
                let uu____6229 = FStar_Syntax_Syntax.bv_to_name x in
                FStar_Syntax_Syntax.as_arg uu____6229 in
              [uu____6228] in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6227 in
          uu____6226 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Util.refine x uu____6225 in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t in
      let uu____6236 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
      if uu____6236
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6254 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6269 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6298)::(ens,uu____6300)::uu____6301 ->
                    let uu____6330 =
                      let uu____6333 = norm1 req in
                      FStar_Pervasives_Native.Some uu____6333 in
                    let uu____6334 =
                      let uu____6335 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens in
                      FStar_All.pipe_left norm1 uu____6335 in
                    (uu____6330, uu____6334)
                | uu____6338 ->
                    let uu____6347 =
                      let uu____6348 =
                        let uu____6353 =
                          let uu____6354 =
                            FStar_Syntax_Print.comp_to_string comp in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____6354 in
                        (uu____6353, (comp.FStar_Syntax_Syntax.pos)) in
                      FStar_Errors.Error uu____6348 in
                    FStar_Exn.raise uu____6347)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6370)::uu____6371 ->
                    let uu____6390 =
                      let uu____6395 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6395 in
                    (match uu____6390 with
                     | (us_r,uu____6427) ->
                         let uu____6428 =
                           let uu____6433 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6433 in
                         (match uu____6428 with
                          | (us_e,uu____6465) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let as_req =
                                let uu____6468 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6468
                                  us_r in
                              let as_ens =
                                let uu____6470 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6470
                                  us_e in
                              let req =
                                let uu____6474 =
                                  let uu____6475 =
                                    let uu____6476 =
                                      let uu____6487 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6487] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6476 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6475 in
                                uu____6474 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let ens =
                                let uu____6505 =
                                  let uu____6506 =
                                    let uu____6507 =
                                      let uu____6518 =
                                        FStar_Syntax_Syntax.as_arg wp in
                                      [uu____6518] in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6507 in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6506 in
                                uu____6505 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
                              let uu____6533 =
                                let uu____6536 = norm1 req in
                                FStar_Pervasives_Native.Some uu____6536 in
                              let uu____6537 =
                                let uu____6538 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens in
                                norm1 uu____6538 in
                              (uu____6533, uu____6537)))
                | uu____6541 -> failwith "Impossible"))
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
      (let uu____6569 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____6569
       then
         let uu____6570 = FStar_Syntax_Print.term_to_string tm in
         let uu____6571 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6570 uu____6571
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
        (let uu____6592 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify") in
         if uu____6592
         then
           let uu____6593 = FStar_Syntax_Print.term_to_string tm in
           let uu____6594 = FStar_Syntax_Print.term_to_string tm' in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6593
             uu____6594
         else ());
        tm'
let remove_reify: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____6600 =
      let uu____6601 =
        let uu____6602 = FStar_Syntax_Subst.compress t in
        uu____6602.FStar_Syntax_Syntax.n in
      match uu____6601 with
      | FStar_Syntax_Syntax.Tm_app uu____6605 -> false
      | uu____6620 -> true in
    if uu____6600
    then t
    else
      (let uu____6622 = FStar_Syntax_Util.head_and_args t in
       match uu____6622 with
       | (head1,args) ->
           let uu____6659 =
             let uu____6660 =
               let uu____6661 = FStar_Syntax_Subst.compress head1 in
               uu____6661.FStar_Syntax_Syntax.n in
             match uu____6660 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6664 -> false in
           if uu____6659
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6686 ->
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
             let uu____6726 = FStar_Syntax_Util.arrow_formals t1 in
             match uu____6726 with
             | (formals,uu____6740) ->
                 let n_implicits =
                   let uu____6758 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6834  ->
                             match uu____6834 with
                             | (uu____6841,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality)))) in
                   match uu____6758 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits in
                 n_implicits in
           let inst_n_binders t1 =
             let uu____6972 = FStar_TypeChecker_Env.expected_typ env in
             match uu____6972 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t in
                 let n_available = number_of_implicits t1 in
                 if n_available < n_expected
                 then
                   let uu____6996 =
                     let uu____6997 =
                       let uu____7002 =
                         let uu____7003 = FStar_Util.string_of_int n_expected in
                         let uu____7010 = FStar_Syntax_Print.term_to_string e in
                         let uu____7011 =
                           FStar_Util.string_of_int n_available in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____7003 uu____7010 uu____7011 in
                       let uu____7018 = FStar_TypeChecker_Env.get_range env in
                       (uu____7002, uu____7018) in
                     FStar_Errors.Error uu____6997 in
                   FStar_Exn.raise uu____6996
                 else FStar_Pervasives_Native.Some (n_available - n_expected) in
           let decr_inst uu___131_7039 =
             match uu___131_7039 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1")) in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7069 = FStar_Syntax_Subst.open_comp bs c in
               (match uu____7069 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_42,uu____7178) when
                          _0_42 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7221,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let uu____7254 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____7254 with
                           | (v1,uu____7294,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1 in
                               let uu____7311 =
                                 aux subst2 (decr_inst inst_n) rest in
                               (match uu____7311 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7404 =
                                      FStar_TypeChecker_Rel.conj_guard g g' in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7404)))
                      | (uu____7431,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard) in
                    let uu____7477 =
                      let uu____7504 = inst_n_binders t in
                      aux [] uu____7504 bs1 in
                    (match uu____7477 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7575) -> (e, torig, guard)
                          | (uu____7606,[]) when
                              let uu____7637 =
                                FStar_Syntax_Util.is_total_comp c1 in
                              Prims.op_Negation uu____7637 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____7638 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7670 ->
                                    FStar_Syntax_Util.arrow bs2 c1 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1 in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos in
                              (e1, t2, guard))))
           | uu____7685 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
let string_of_univs:
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string =
  fun univs1  ->
    let uu____7694 =
      let uu____7697 = FStar_Util.set_elements univs1 in
      FStar_All.pipe_right uu____7697
        (FStar_List.map
           (fun u  ->
              let uu____7707 = FStar_Syntax_Unionfind.univ_uvar_id u in
              FStar_All.pipe_right uu____7707 FStar_Util.string_of_int)) in
    FStar_All.pipe_right uu____7694 (FStar_String.concat ", ")
let gen_univs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____7726 = FStar_Util.set_is_empty x in
      if uu____7726
      then []
      else
        (let s =
           let uu____7733 =
             let uu____7736 = FStar_TypeChecker_Env.univ_vars env in
             FStar_Util.set_difference x uu____7736 in
           FStar_All.pipe_right uu____7733 FStar_Util.set_elements in
         (let uu____7744 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen") in
          if uu____7744
          then
            let uu____7745 =
              let uu____7746 = FStar_TypeChecker_Env.univ_vars env in
              string_of_univs uu____7746 in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7745
          else ());
         (let r =
            let uu____7753 = FStar_TypeChecker_Env.get_range env in
            FStar_Pervasives_Native.Some uu____7753 in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r in
                    (let uu____7768 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen") in
                     if uu____7768
                     then
                       let uu____7769 =
                         let uu____7770 =
                           FStar_Syntax_Unionfind.univ_uvar_id u in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7770 in
                       let uu____7771 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u) in
                       let uu____7772 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name) in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7769 uu____7771 uu____7772
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
        let uu____7796 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames in
        FStar_All.pipe_right uu____7796 FStar_Util.fifo_set_elements in
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
        | ([],uu____7831) -> generalized_univ_names
        | (uu____7838,[]) -> explicit_univ_names
        | uu____7845 ->
            let uu____7854 =
              let uu____7855 =
                let uu____7860 =
                  let uu____7861 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____7861 in
                (uu____7860, (t.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7855 in
            FStar_Exn.raise uu____7854
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
      (let uu____7880 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen") in
       if uu____7880
       then
         let uu____7881 = string_of_univs univs1 in
         FStar_Util.print1 "univs to gen : %s\n" uu____7881
       else ());
      (let gen1 = gen_univs env univs1 in
       (let uu____7887 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen") in
        if uu____7887
        then
          let uu____7888 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.print1 "After generalization: %s\n" uu____7888
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
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple4 Prims.list
          FStar_Pervasives_Native.option
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____7953 =
          let uu____7954 =
            FStar_Util.for_all
              (fun uu____7967  ->
                 match uu____7967 with
                 | (uu____7976,uu____7977,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs in
          FStar_All.pipe_left Prims.op_Negation uu____7954 in
        if uu____7953
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8015 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium in
              if uu____8015
              then
                let uu____8016 = FStar_Syntax_Print.comp_to_string c in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8016
              else ());
             (let c1 =
                let uu____8019 = FStar_TypeChecker_Env.should_verify env in
                if uu____8019
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
              (let uu____8022 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium in
               if uu____8022
               then
                 let uu____8023 = FStar_Syntax_Print.comp_to_string c1 in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8023
               else ());
              c1) in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env in
           let gen_uvars uvs =
             let uu____8084 = FStar_Util.set_difference uvs env_uvars in
             FStar_All.pipe_right uu____8084 FStar_Util.set_elements in
           let univs_and_uvars_of_lec uu____8214 =
             match uu____8214 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress in
                 let c1 = norm1 c in
                 let t1 = FStar_Syntax_Util.comp_result c1 in
                 let univs1 = FStar_Syntax_Free.univs t1 in
                 let uvt = FStar_Syntax_Free.uvars t1 in
                 ((let uu____8280 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen") in
                   if uu____8280
                   then
                     let uu____8281 =
                       let uu____8282 =
                         let uu____8285 = FStar_Util.set_elements univs1 in
                         FStar_All.pipe_right uu____8285
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u))) in
                       FStar_All.pipe_right uu____8282
                         (FStar_String.concat ", ") in
                     let uu____8312 =
                       let uu____8313 =
                         let uu____8316 = FStar_Util.set_elements uvt in
                         FStar_All.pipe_right uu____8316
                           (FStar_List.map
                              (fun uu____8344  ->
                                 match uu____8344 with
                                 | (u,t2) ->
                                     let uu____8351 =
                                       FStar_Syntax_Print.uvar_to_string u in
                                     let uu____8352 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8351 uu____8352)) in
                       FStar_All.pipe_right uu____8313
                         (FStar_String.concat ", ") in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8281
                       uu____8312
                   else ());
                  (let univs2 =
                     let uu____8359 = FStar_Util.set_elements uvt in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8382  ->
                            match uu____8382 with
                            | (uu____8391,t2) ->
                                let uu____8393 = FStar_Syntax_Free.univs t2 in
                                FStar_Util.set_union univs2 uu____8393)
                       univs1 uu____8359 in
                   let uvs = gen_uvars uvt in
                   (let uu____8416 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen") in
                    if uu____8416
                    then
                      let uu____8417 =
                        let uu____8418 =
                          let uu____8421 = FStar_Util.set_elements univs2 in
                          FStar_All.pipe_right uu____8421
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u))) in
                        FStar_All.pipe_right uu____8418
                          (FStar_String.concat ", ") in
                      let uu____8448 =
                        let uu____8449 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8481  ->
                                  match uu____8481 with
                                  | (u,t2) ->
                                      let uu____8488 =
                                        FStar_Syntax_Print.uvar_to_string u in
                                      let uu____8489 =
                                        FStar_Syntax_Print.term_to_string t2 in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8488 uu____8489)) in
                        FStar_All.pipe_right uu____8449
                          (FStar_String.concat ", ") in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8417
                        uu____8448
                    else ());
                   (univs2, uvs, (lbname, e, c1)))) in
           let uu____8519 =
             let uu____8552 = FStar_List.hd lecs in
             univs_and_uvars_of_lec uu____8552 in
           match uu____8519 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8666 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1) in
                 if uu____8666
                 then ()
                 else
                   (let uu____8668 = lec_hd in
                    match uu____8668 with
                    | (lb1,uu____8676,uu____8677) ->
                        let uu____8678 = lec2 in
                        (match uu____8678 with
                         | (lb2,uu____8686,uu____8687) ->
                             let msg =
                               let uu____8689 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8690 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8689 uu____8690 in
                             let uu____8691 =
                               let uu____8692 =
                                 let uu____8697 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8697) in
                               FStar_Errors.Error uu____8692 in
                             FStar_Exn.raise uu____8691)) in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____8808  ->
                           match uu____8808 with
                           | (u,uu____8816) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____8838  ->
                                       match uu____8838 with
                                       | (u',uu____8846) ->
                                           FStar_Syntax_Unionfind.equiv u u')))) in
                 let uu____8851 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1) in
                 if uu____8851
                 then ()
                 else
                   (let uu____8853 = lec_hd in
                    match uu____8853 with
                    | (lb1,uu____8861,uu____8862) ->
                        let uu____8863 = lec2 in
                        (match uu____8863 with
                         | (lb2,uu____8871,uu____8872) ->
                             let msg =
                               let uu____8874 =
                                 FStar_Syntax_Print.lbname_to_string lb1 in
                               let uu____8875 =
                                 FStar_Syntax_Print.lbname_to_string lb2 in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8874 uu____8875 in
                             let uu____8876 =
                               let uu____8877 =
                                 let uu____8882 =
                                   FStar_TypeChecker_Env.get_range env in
                                 (msg, uu____8882) in
                               FStar_Errors.Error uu____8877 in
                             FStar_Exn.raise uu____8876)) in
               let lecs1 =
                 let uu____8892 = FStar_List.tl lecs in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8951 = univs_and_uvars_of_lec this_lec in
                        match uu____8951 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8892 [] in
               let lecs2 = lec_hd :: lecs1 in
               let gen_types uvs1 =
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9129  ->
                         match uu____9129 with
                         | (u,k) ->
                             let uu____9142 = FStar_Syntax_Unionfind.find u in
                             (match uu____9142 with
                              | FStar_Pervasives_Native.Some uu____9151 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9158 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k in
                                  let uu____9162 =
                                    FStar_Syntax_Util.arrow_formals k1 in
                                  (match uu____9162 with
                                   | (bs,kres) ->
                                       let a =
                                         let uu____9200 =
                                           let uu____9203 =
                                             FStar_TypeChecker_Env.get_range
                                               env in
                                           FStar_All.pipe_left
                                             (fun _0_43  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_43) uu____9203 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____9200 kres in
                                       let t =
                                         let uu____9207 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Util.abs bs uu____9207
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 kres)) in
                                       (FStar_Syntax_Util.set_uvar u t;
                                        (a,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag))))))) in
               let gen_univs1 = gen_univs env univs1 in
               let gen_tvars = gen_types uvs in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9295  ->
                         match uu____9295 with
                         | (lbname,e,c) ->
                             let uu____9331 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | uu____9366 ->
                                   let uu____9381 = (e, c) in
                                   (match uu____9381 with
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
                                                (fun uu____9408  ->
                                                   match uu____9408 with
                                                   | (x,uu____9416) ->
                                                       let uu____9421 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9421)
                                                gen_tvars in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9431 =
                                                let uu____9432 =
                                                  FStar_Util.right lbname in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9432 in
                                              if uu____9431
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
                                          let uu____9440 =
                                            let uu____9441 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1) in
                                            uu____9441.FStar_Syntax_Syntax.n in
                                          match uu____9440 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9464 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod in
                                              (match uu____9464 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9479 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1 in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1)) in
                                        let uu____9481 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        (e', uu____9481)) in
                             (match uu____9331 with
                              | (e1,c1) -> (lbname, gen_univs1, e1, c1)))) in
               FStar_Pervasives_Native.Some ecs)
let generalize:
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____9569 = Obj.magic () in ());
        (let uu____9571 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____9571
         then
           let uu____9572 =
             let uu____9573 =
               FStar_List.map
                 (fun uu____9586  ->
                    match uu____9586 with
                    | (lb,uu____9594,uu____9595) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs in
             FStar_All.pipe_right uu____9573 (FStar_String.concat ", ") in
           FStar_Util.print1 "Generalizing: %s\n" uu____9572
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9616  ->
                match uu____9616 with
                | (l,t,c) -> gather_free_univnames env t) lecs in
         let generalized_lecs =
           let uu____9641 = gen env is_rec lecs in
           match uu____9641 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9720  ->
                       match uu____9720 with | (l,t,c) -> (l, [], t, c)))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9768 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium in
                 if uu____9768
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9804  ->
                           match uu____9804 with
                           | (l,us,e,c) ->
                               let uu____9835 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos in
                               let uu____9836 =
                                 FStar_Syntax_Print.lbname_to_string l in
                               let uu____9837 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c) in
                               let uu____9838 =
                                 FStar_Syntax_Print.term_to_string e in
                               FStar_Util.print4
                                 "(%s) Generalized %s at type %s\n%s\n"
                                 uu____9835 uu____9836 uu____9837 uu____9838))
                 else ());
                luecs) in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9870  ->
                match uu____9870 with
                | (l,generalized_univs,t,c) ->
                    let uu____9901 =
                      check_universe_generalization univnames1
                        generalized_univs t in
                    (l, uu____9901, t, c)) univnames_lecs generalized_lecs)
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
              (let uu____9946 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21 in
               match uu____9946 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9952 = FStar_TypeChecker_Rel.apply_guard f e in
                   FStar_All.pipe_left
                     (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                     uu____9952) in
          let is_var e1 =
            let uu____9959 =
              let uu____9960 = FStar_Syntax_Subst.compress e1 in
              uu____9960.FStar_Syntax_Syntax.n in
            match uu____9959 with
            | FStar_Syntax_Syntax.Tm_name uu____9963 -> true
            | uu____9964 -> false in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1 in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___172_9980 = x in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___172_9980.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___172_9980.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9981 -> e2 in
          let env2 =
            let uu___173_9983 = env1 in
            let uu____9984 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e)) in
            {
              FStar_TypeChecker_Env.solver =
                (uu___173_9983.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___173_9983.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___173_9983.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___173_9983.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___173_9983.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___173_9983.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___173_9983.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___173_9983.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___173_9983.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___173_9983.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___173_9983.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___173_9983.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___173_9983.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___173_9983.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___173_9983.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9984;
              FStar_TypeChecker_Env.is_iface =
                (uu___173_9983.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___173_9983.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___173_9983.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___173_9983.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___173_9983.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___173_9983.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___173_9983.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___173_9983.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___173_9983.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___173_9983.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___173_9983.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___173_9983.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___173_9983.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___173_9983.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___173_9983.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___173_9983.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___173_9983.FStar_TypeChecker_Env.dsenv)
            } in
          let uu____9985 = check env2 t1 t2 in
          match uu____9985 with
          | FStar_Pervasives_Native.None  ->
              let uu____9992 =
                let uu____9993 =
                  let uu____9998 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1 in
                  let uu____9999 = FStar_TypeChecker_Env.get_range env2 in
                  (uu____9998, uu____9999) in
                FStar_Errors.Error uu____9993 in
              FStar_Exn.raise uu____9992
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10006 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel") in
                if uu____10006
                then
                  let uu____10007 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10007
                else ());
               (let uu____10009 = decorate e t2 in (uu____10009, g)))
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
        let uu____10040 = FStar_Syntax_Util.is_total_lcomp lc in
        if uu____10040
        then
          let uu____10045 = discharge g1 in
          let uu____10046 = lc.FStar_Syntax_Syntax.comp () in
          (uu____10045, uu____10046)
        else
          (let c = lc.FStar_Syntax_Syntax.comp () in
           let steps = [FStar_TypeChecker_Normalize.Beta] in
           let c1 =
             let uu____10059 =
               let uu____10060 =
                 let uu____10061 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c in
                 FStar_All.pipe_right uu____10061 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____10060
                 (FStar_TypeChecker_Normalize.normalize_comp steps env) in
             FStar_All.pipe_right uu____10059
               (FStar_TypeChecker_Env.comp_to_comp_typ env) in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name in
           let uu____10063 = destruct_comp c1 in
           match uu____10063 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10080 = FStar_TypeChecker_Env.get_range env in
                 let uu____10081 =
                   let uu____10082 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial in
                   let uu____10083 =
                     let uu____10084 = FStar_Syntax_Syntax.as_arg t in
                     let uu____10085 =
                       let uu____10088 = FStar_Syntax_Syntax.as_arg wp in
                       [uu____10088] in
                     uu____10084 :: uu____10085 in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10082 uu____10083 in
                 uu____10081 FStar_Pervasives_Native.None uu____10080 in
               ((let uu____10092 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification") in
                 if uu____10092
                 then
                   let uu____10093 = FStar_Syntax_Print.term_to_string vc in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10093
                 else ());
                (let g2 =
                   let uu____10096 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc) in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10096 in
                 let uu____10097 = discharge g2 in
                 let uu____10098 = FStar_Syntax_Syntax.mk_Comp c1 in
                 (uu____10097, uu____10098))))
let short_circuit:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___132_10124 =
        match uu___132_10124 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10132)::[] -> f fst1
        | uu____10149 -> failwith "Unexpexted args to binary operator" in
      let op_and_e e =
        let uu____10154 = FStar_Syntax_Util.b2t e in
        FStar_All.pipe_right uu____10154
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45) in
      let op_or_e e =
        let uu____10163 =
          let uu____10166 = FStar_Syntax_Util.b2t e in
          FStar_Syntax_Util.mk_neg uu____10166 in
        FStar_All.pipe_right uu____10163
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46) in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47) in
      let op_or_t t =
        let uu____10177 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg in
        FStar_All.pipe_right uu____10177
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48) in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49) in
      let short_op_ite uu___133_10191 =
        match uu___133_10191 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10199)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10218)::[] ->
            let uu____10247 = FStar_Syntax_Util.mk_neg guard in
            FStar_All.pipe_right uu____10247
              (fun _0_50  -> FStar_TypeChecker_Common.NonTrivial _0_50)
        | uu____10252 -> failwith "Unexpected args to ITE" in
      let table =
        let uu____10262 =
          let uu____10269 = short_bin_op op_and_e in
          (FStar_Parser_Const.op_And, uu____10269) in
        let uu____10274 =
          let uu____10283 =
            let uu____10290 = short_bin_op op_or_e in
            (FStar_Parser_Const.op_Or, uu____10290) in
          let uu____10295 =
            let uu____10304 =
              let uu____10311 = short_bin_op op_and_t in
              (FStar_Parser_Const.and_lid, uu____10311) in
            let uu____10316 =
              let uu____10325 =
                let uu____10332 = short_bin_op op_or_t in
                (FStar_Parser_Const.or_lid, uu____10332) in
              let uu____10337 =
                let uu____10346 =
                  let uu____10353 = short_bin_op op_imp_t in
                  (FStar_Parser_Const.imp_lid, uu____10353) in
                [uu____10346; (FStar_Parser_Const.ite_lid, short_op_ite)] in
              uu____10325 :: uu____10337 in
            uu____10304 :: uu____10316 in
          uu____10283 :: uu____10295 in
        uu____10262 :: uu____10274 in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____10404 =
            FStar_Util.find_map table
              (fun uu____10417  ->
                 match uu____10417 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____10434 = mk1 seen_args in
                       FStar_Pervasives_Native.Some uu____10434
                     else FStar_Pervasives_Native.None) in
          (match uu____10404 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10437 -> FStar_TypeChecker_Common.Trivial
let short_circuit_head: FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____10442 =
      let uu____10443 = FStar_Syntax_Util.un_uinst l in
      uu____10443.FStar_Syntax_Syntax.n in
    match uu____10442 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10447 -> false
let maybe_add_implicit_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10473)::uu____10474 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10485 -> FStar_TypeChecker_Env.get_range env in
      match bs with
      | (uu____10492,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10493))::uu____10494 -> bs
      | uu____10511 ->
          let uu____10512 = FStar_TypeChecker_Env.expected_typ env in
          (match uu____10512 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10516 =
                 let uu____10517 = FStar_Syntax_Subst.compress t in
                 uu____10517.FStar_Syntax_Syntax.n in
               (match uu____10516 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10521) ->
                    let uu____10538 =
                      FStar_Util.prefix_until
                        (fun uu___134_10578  ->
                           match uu___134_10578 with
                           | (uu____10585,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10586)) ->
                               false
                           | uu____10589 -> true) bs' in
                    (match uu____10538 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10624,uu____10625) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10697,uu____10698) ->
                         let uu____10771 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10789  ->
                                   match uu____10789 with
                                   | (x,uu____10797) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'")) in
                         if uu____10771
                         then
                           let r = pos bs in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10844  ->
                                     match uu____10844 with
                                     | (x,i) ->
                                         let uu____10863 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r in
                                         (uu____10863, i))) in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10873 -> bs))
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
          let uu____10914 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid) in
          if uu____10914
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
        (let uu____10941 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____10941
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____10943 = FStar_Syntax_Print.term_to_string def in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____10943))
         else ());
        (let fv =
           let uu____10946 = FStar_Syntax_Util.incr_delta_qualifier def in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10946
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
         let uu____10954 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange in
         ((let uu___174_10960 = sig_ctx in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___174_10960.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___174_10960.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___174_10960.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___174_10960.FStar_Syntax_Syntax.sigattrs)
           }), uu____10954))
let check_sigelt_quals:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___135_10972 =
        match uu___135_10972 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10973 -> false in
      let reducibility uu___136_10977 =
        match uu___136_10977 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10978 -> false in
      let assumption uu___137_10982 =
        match uu___137_10982 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10983 -> false in
      let reification uu___138_10987 =
        match uu___138_10987 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10988 -> true
        | uu____10989 -> false in
      let inferred uu___139_10993 =
        match uu___139_10993 with
        | FStar_Syntax_Syntax.Discriminator uu____10994 -> true
        | FStar_Syntax_Syntax.Projector uu____10995 -> true
        | FStar_Syntax_Syntax.RecordType uu____11000 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11009 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11018 -> false in
      let has_eq uu___140_11022 =
        match uu___140_11022 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11023 -> false in
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
        | FStar_Syntax_Syntax.Reflectable uu____11083 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11088 -> true in
      let quals = FStar_Syntax_Util.quals_of_sigelt se in
      let uu____11092 =
        let uu____11093 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___141_11097  ->
                  match uu___141_11097 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11098 -> false)) in
        FStar_All.pipe_right uu____11093 Prims.op_Negation in
      if uu____11092
      then
        let r = FStar_Syntax_Util.range_of_sigelt se in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals in
        let err' msg =
          let uu____11111 =
            let uu____11112 =
              let uu____11117 =
                let uu____11118 = FStar_Syntax_Print.quals_to_string quals in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____11118 msg in
              (uu____11117, r) in
            FStar_Errors.Error uu____11112 in
          FStar_Exn.raise uu____11111 in
        let err1 msg = err' (Prims.strcat ": " msg) in
        let err'1 uu____11126 = err' "" in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err1 "duplicate qualifiers"
         else ();
         (let uu____11130 =
            let uu____11131 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals)) in
            Prims.op_Negation uu____11131 in
          if uu____11130 then err1 "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11136),uu____11137) ->
              ((let uu____11153 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) in
                if uu____11153
                then err1 "recursive definitions cannot be marked inline"
                else ());
               (let uu____11157 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x))) in
                if uu____11157
                then
                  err1
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11163 ->
              let uu____11172 =
                let uu____11173 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x))) in
                Prims.op_Negation uu____11173 in
              if uu____11172 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11179 ->
              let uu____11186 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq) in
              if uu____11186 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11190 ->
              let uu____11197 =
                let uu____11198 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption))) in
                Prims.op_Negation uu____11198 in
              if uu____11197 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11204 ->
              let uu____11205 =
                let uu____11206 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11206 in
              if uu____11205 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11212 ->
              let uu____11213 =
                let uu____11214 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x))) in
                Prims.op_Negation uu____11214 in
              if uu____11213 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11220 ->
              let uu____11233 =
                let uu____11234 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x))) in
                Prims.op_Negation uu____11234 in
              if uu____11233 then err'1 () else ()
          | uu____11240 -> ()))
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
                          let uu____11313 =
                            let uu____11316 =
                              let uu____11317 =
                                let uu____11324 =
                                  let uu____11325 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11325 in
                                (uu____11324, inst_univs) in
                              FStar_Syntax_Syntax.Tm_uinst uu____11317 in
                            FStar_Syntax_Syntax.mk uu____11316 in
                          uu____11313 FStar_Pervasives_Native.None p in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11366  ->
                                  match uu____11366 with
                                  | (x,imp) ->
                                      let uu____11377 =
                                        FStar_Syntax_Syntax.bv_to_name x in
                                      (uu____11377, imp))) in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p in
                      let unrefined_arg_binder =
                        let uu____11379 = projectee arg_typ in
                        FStar_Syntax_Syntax.mk_binder uu____11379 in
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
                             let uu____11388 =
                               let uu____11389 =
                                 let uu____11390 =
                                   let uu____11391 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs in
                                   let uu____11392 =
                                     let uu____11393 =
                                       let uu____11394 =
                                         FStar_Syntax_Syntax.bv_to_name x in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11394 in
                                     [uu____11393] in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11391
                                     uu____11392 in
                                 uu____11390 FStar_Pervasives_Native.None p in
                               FStar_Syntax_Util.b2t uu____11389 in
                             FStar_Syntax_Util.refine x uu____11388 in
                           let uu____11397 =
                             let uu___175_11398 = projectee arg_typ in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___175_11398.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___175_11398.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             } in
                           FStar_Syntax_Syntax.mk_binder uu____11397) in
                      let ntps = FStar_List.length tps in
                      let all_params =
                        let uu____11413 =
                          FStar_List.map
                            (fun uu____11435  ->
                               match uu____11435 with
                               | (x,uu____11447) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps in
                        FStar_List.append uu____11413 fields in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____11496  ->
                                match uu____11496 with
                                | (x,uu____11508) ->
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
                             (let uu____11522 =
                                FStar_TypeChecker_Env.current_module env in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____11522)
                               ||
                               (let uu____11524 =
                                  let uu____11525 =
                                    FStar_TypeChecker_Env.current_module env in
                                  uu____11525.FStar_Ident.str in
                                FStar_Options.dont_gen_projectors uu____11524) in
                           let quals =
                             let uu____11529 =
                               let uu____11532 =
                                 let uu____11535 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit) in
                                 if uu____11535
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else [] in
                               let uu____11539 =
                                 FStar_List.filter
                                   (fun uu___142_11543  ->
                                      match uu___142_11543 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____11544 -> false) iquals in
                               FStar_List.append uu____11532 uu____11539 in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____11529 in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder] in
                           let t =
                             let bool_typ =
                               let uu____11565 =
                                 let uu____11566 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None in
                                 FStar_Syntax_Syntax.fv_to_tm uu____11566 in
                               FStar_Syntax_Syntax.mk_Total uu____11565 in
                             let uu____11567 =
                               FStar_Syntax_Util.arrow binders bool_typ in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____11567 in
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
                           (let uu____11570 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes") in
                            if uu____11570
                            then
                              let uu____11571 =
                                FStar_Syntax_Print.sigelt_to_string decl in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____11571
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
                                             fun uu____11624  ->
                                               match uu____11624 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____11648 =
                                                       let uu____11651 =
                                                         let uu____11652 =
                                                           let uu____11659 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun in
                                                           (uu____11659,
                                                             FStar_Syntax_Syntax.tun) in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____11652 in
                                                       pos uu____11651 in
                                                     (uu____11648, b)
                                                   else
                                                     (let uu____11663 =
                                                        let uu____11666 =
                                                          let uu____11667 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____11667 in
                                                        pos uu____11666 in
                                                      (uu____11663, b)))) in
                                   let pat_true =
                                     let uu____11685 =
                                       let uu____11688 =
                                         let uu____11689 =
                                           let uu____11702 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq) in
                                           (uu____11702, arg_pats) in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____11689 in
                                       pos uu____11688 in
                                     (uu____11685,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool) in
                                   let pat_false =
                                     let uu____11736 =
                                       let uu____11739 =
                                         let uu____11740 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____11740 in
                                       pos uu____11739 in
                                     (uu____11736,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool) in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder) in
                                   let uu____11752 =
                                     let uu____11755 =
                                       let uu____11756 =
                                         let uu____11779 =
                                           let uu____11782 =
                                             FStar_Syntax_Util.branch
                                               pat_true in
                                           let uu____11783 =
                                             let uu____11786 =
                                               FStar_Syntax_Util.branch
                                                 pat_false in
                                             [uu____11786] in
                                           uu____11782 :: uu____11783 in
                                         (arg_exp, uu____11779) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11756 in
                                     FStar_Syntax_Syntax.mk uu____11755 in
                                   uu____11752 FStar_Pervasives_Native.None p) in
                              let dd =
                                let uu____11793 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract) in
                                if uu____11793
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
                                let uu____11801 =
                                  let uu____11806 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None in
                                  FStar_Util.Inr uu____11806 in
                                let uu____11807 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____11801;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____11807
                                } in
                              let impl =
                                let uu____11811 =
                                  let uu____11812 =
                                    let uu____11819 =
                                      let uu____11822 =
                                        let uu____11823 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right in
                                        FStar_All.pipe_right uu____11823
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                      [uu____11822] in
                                    ((false, [lb]), uu____11819) in
                                  FStar_Syntax_Syntax.Sig_let uu____11812 in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____11811;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                } in
                              (let uu____11841 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes") in
                               if uu____11841
                               then
                                 let uu____11842 =
                                   FStar_Syntax_Print.sigelt_to_string impl in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____11842
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
                                fun uu____11884  ->
                                  match uu____11884 with
                                  | (a,uu____11890) ->
                                      let uu____11891 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i in
                                      (match uu____11891 with
                                       | (field_name,uu____11897) ->
                                           let field_proj_tm =
                                             let uu____11899 =
                                               let uu____11900 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____11900 in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____11899 inst_univs in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p in
                                           FStar_Syntax_Syntax.NT (a, proj)))) in
                      let projectors_ses =
                        let uu____11917 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____11949  ->
                                    match uu____11949 with
                                    | (x,uu____11957) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x in
                                        let uu____11959 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i in
                                        (match uu____11959 with
                                         | (field_name,uu____11967) ->
                                             let t =
                                               let uu____11969 =
                                                 let uu____11970 =
                                                   let uu____11973 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____11973 in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____11970 in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____11969 in
                                             let only_decl =
                                               (let uu____11977 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____11977)
                                                 ||
                                                 (let uu____11979 =
                                                    let uu____11980 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env in
                                                    uu____11980.FStar_Ident.str in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____11979) in
                                             let no_decl = false in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____11994 =
                                                   FStar_List.filter
                                                     (fun uu___143_11998  ->
                                                        match uu___143_11998
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____11999 -> true)
                                                     q in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____11994
                                               else q in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___144_12012  ->
                                                         match uu___144_12012
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12013 ->
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
                                             ((let uu____12032 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes") in
                                               if uu____12032
                                               then
                                                 let uu____12033 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12033
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
                                                           fun uu____12081 
                                                             ->
                                                             match uu____12081
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12105
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection) in
                                                                   (uu____12105,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12121
                                                                    =
                                                                    let uu____12124
                                                                    =
                                                                    let uu____12125
                                                                    =
                                                                    let uu____12132
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    (uu____12132,
                                                                    FStar_Syntax_Syntax.tun) in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12125 in
                                                                    pos
                                                                    uu____12124 in
                                                                    (uu____12121,
                                                                    b))
                                                                   else
                                                                    (let uu____12136
                                                                    =
                                                                    let uu____12139
                                                                    =
                                                                    let uu____12140
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12140 in
                                                                    pos
                                                                    uu____12139 in
                                                                    (uu____12136,
                                                                    b)))) in
                                                 let pat =
                                                   let uu____12156 =
                                                     let uu____12159 =
                                                       let uu____12160 =
                                                         let uu____12173 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq) in
                                                         (uu____12173,
                                                           arg_pats) in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12160 in
                                                     pos uu____12159 in
                                                   let uu____12182 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection in
                                                   (uu____12156,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12182) in
                                                 let body =
                                                   let uu____12194 =
                                                     let uu____12197 =
                                                       let uu____12198 =
                                                         let uu____12221 =
                                                           let uu____12224 =
                                                             FStar_Syntax_Util.branch
                                                               pat in
                                                           [uu____12224] in
                                                         (arg_exp,
                                                           uu____12221) in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12198 in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12197 in
                                                   uu____12194
                                                     FStar_Pervasives_Native.None
                                                     p1 in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None in
                                                 let dd =
                                                   let uu____12232 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract) in
                                                   if uu____12232
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
                                                   let uu____12239 =
                                                     let uu____12244 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None in
                                                     FStar_Util.Inr
                                                       uu____12244 in
                                                   let uu____12245 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12239;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12245
                                                   } in
                                                 let impl =
                                                   let uu____12249 =
                                                     let uu____12250 =
                                                       let uu____12257 =
                                                         let uu____12260 =
                                                           let uu____12261 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right in
                                                           FStar_All.pipe_right
                                                             uu____12261
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                                         [uu____12260] in
                                                       ((false, [lb]),
                                                         uu____12257) in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12250 in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12249;
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
                                                 (let uu____12279 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes") in
                                                  if uu____12279
                                                  then
                                                    let uu____12280 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12280
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl]))))) in
                        FStar_All.pipe_right uu____11917 FStar_List.flatten in
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12324) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12329 = FStar_Syntax_Subst.univ_var_opening uvs in
              (match uu____12329 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t in
                   let uu____12351 = FStar_Syntax_Util.arrow_formals t1 in
                   (match uu____12351 with
                    | (formals,uu____12367) ->
                        let uu____12384 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____12416 =
                                   let uu____12417 =
                                     let uu____12418 =
                                       FStar_Syntax_Util.lid_of_sigelt se1 in
                                     FStar_Util.must uu____12418 in
                                   FStar_Ident.lid_equals typ_lid uu____12417 in
                                 if uu____12416
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____12437,uvs',tps,typ0,uu____12441,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____12460 -> failwith "Impossible"
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
                        (match uu____12384 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0 in
                             let uu____12533 =
                               FStar_Syntax_Util.arrow_formals typ01 in
                             (match uu____12533 with
                              | (indices,uu____12549) ->
                                  let refine_domain =
                                    let uu____12567 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___145_12572  ->
                                              match uu___145_12572 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____12573 -> true
                                              | uu____12582 -> false)) in
                                    if uu____12567
                                    then false
                                    else should_refine in
                                  let fv_qual =
                                    let filter_records uu___146_12590 =
                                      match uu___146_12590 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____12593,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____12605 ->
                                          FStar_Pervasives_Native.None in
                                    let uu____12606 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records in
                                    match uu____12606 with
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
                                    let uu____12617 =
                                      FStar_Util.first_N n_typars formals in
                                    match uu____12617 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____12682  ->
                                               fun uu____12683  ->
                                                 match (uu____12682,
                                                         uu____12683)
                                                 with
                                                 | ((x,uu____12701),(x',uu____12703))
                                                     ->
                                                     let uu____12712 =
                                                       let uu____12719 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x' in
                                                       (x, uu____12719) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____12712) imp_tps
                                            inductive_tps1 in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____12720 -> []