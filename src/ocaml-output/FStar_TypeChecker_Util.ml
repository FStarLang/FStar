open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit) =
  fun env  ->
    fun errs  ->
      let uu____17 = FStar_TypeChecker_Env.get_range env  in
      let uu____18 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____17 uu____18
  
let (is_type : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26 =
      let uu____27 = FStar_Syntax_Subst.compress t  in
      uu____27.FStar_Syntax_Syntax.n  in
    match uu____26 with
    | FStar_Syntax_Syntax.Tm_type uu____30 -> true
    | uu____31 -> false
  
let (t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    let uu____41 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____41
      (FStar_List.filter
         (fun uu____55  ->
            match uu____55 with
            | (x,uu____61) -> is_type x.FStar_Syntax_Syntax.sort))
  
let (new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____73 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____75 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____75)
           in
        if uu____73
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____77 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Rel.new_uvar uu____77 bs k
  
let (new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____84 = new_uvar_aux env k  in
      FStar_Pervasives_Native.fst uu____84
  
let (as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar) =
  fun uu___80_93  ->
    match uu___80_93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____95);
        FStar_Syntax_Syntax.pos = uu____96;
        FStar_Syntax_Syntax.vars = uu____97;_} -> uv
    | uu____124 -> failwith "Impossible"
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____149 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____149 with
          | FStar_Pervasives_Native.Some (uu____172::(tm,uu____174)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____226 ->
              let uu____237 = new_uvar_aux env k  in
              (match uu____237 with
               | (t,u) ->
                   let g =
                     let uu___104_257 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____258 =
                       let uu____273 =
                         let uu____286 = as_uvar u  in
                         (reason, env, uu____286, t, k, r)  in
                       [uu____273]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___104_257.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___104_257.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___104_257.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____258
                     }  in
                   let uu____311 =
                     let uu____318 =
                       let uu____323 = as_uvar u  in (uu____323, r)  in
                     [uu____318]  in
                   (t, uu____311, g))
  
let (check_uvars :
  FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____351 =
        let uu____352 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____352  in
      if uu____351
      then
        let us =
          let uu____358 =
            let uu____361 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____379  ->
                 match uu____379 with
                 | (x,uu____385) -> FStar_Syntax_Print.uvar_to_string x)
              uu____361
             in
          FStar_All.pipe_right uu____358 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____392 =
            let uu____397 =
              let uu____398 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____398
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____397)  in
          FStar_Errors.log_issue r uu____392);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____411  ->
      match uu____411 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____421;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____423;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder1 scope a =
                   let uu____472 =
                     let uu____473 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____473.FStar_Syntax_Syntax.n  in
                   match uu____472 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____480 = FStar_Syntax_Util.type_u ()  in
                       (match uu____480 with
                        | (k,uu____490) ->
                            let t2 =
                              let uu____492 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____492
                                FStar_Pervasives_Native.fst
                               in
                            ((let uu___105_502 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___105_502.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___105_502.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____503 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____540) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____547) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____610) ->
                       let uu____631 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____691  ->
                                 fun uu____692  ->
                                   match (uu____691, uu____692) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____770 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____770 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____631 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____882 = aux must_check_ty1 scope body  in
                            (match uu____882 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____911 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____911
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____918 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____918
                                   then
                                     let uu____919 =
                                       FStar_Range.string_of_range r  in
                                     let uu____920 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____921 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____919 uu____920 uu____921
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____931 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____945 =
                            let uu____950 =
                              let uu____951 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____951
                                FStar_Pervasives_Native.fst
                               in
                            FStar_Util.Inl uu____950  in
                          (uu____945, false))
                    in
                 let uu____964 =
                   let uu____973 = t_binders env  in aux false uu____973 e
                    in
                 match uu____964 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____998 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____998
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1002 =
                                let uu____1007 =
                                  let uu____1008 =
                                    FStar_Syntax_Print.comp_to_string c  in
                                  FStar_Util.format1
                                    "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                    uu____1008
                                   in
                                (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                  uu____1007)
                                 in
                              FStar_Errors.raise_error uu____1002 rng)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____1016 ->
               let uu____1017 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1017 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (pat_as_exp :
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
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____1097 =
              let uu____1102 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1102 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1107;
                  FStar_Syntax_Syntax.vars = uu____1108;_} ->
                  let uu____1111 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1111 with
                   | (t,uu____1121) ->
                       let uu____1122 = new_uvar env1 t  in
                       (uu____1122, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1097 with
            | (t_x,guard) ->
                ((let uu___106_1131 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___106_1131.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___106_1131.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard)
             in
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
                  | uu____1200 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1208) ->
                let uu____1213 = FStar_Syntax_Util.type_u ()  in
                (match uu____1213 with
                 | (k,uu____1239) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___107_1242 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___107_1242.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___107_1242.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1243 =
                       let uu____1248 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1248 t
                        in
                     (match uu____1243 with
                      | (e,u) ->
                          let p2 =
                            let uu___108_1274 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___108_1274.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1284 = check_bv env1 x  in
                (match uu____1284 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1325 = check_bv env1 x  in
                (match uu____1325 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1382 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1518  ->
                          fun uu____1519  ->
                            match (uu____1518, uu____1519) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1717 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1717 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1793 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1793, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1382 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1924 =
                         let uu____1927 =
                           let uu____1928 =
                             let uu____1935 =
                               let uu____1938 =
                                 let uu____1939 =
                                   FStar_Syntax_Syntax.fv_to_tm fv  in
                                 let uu____1940 =
                                   FStar_All.pipe_right args FStar_List.rev
                                    in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____1939
                                   uu____1940
                                  in
                               uu____1938 FStar_Pervasives_Native.None
                                 p1.FStar_Syntax_Syntax.p
                                in
                             (uu____1935,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Data_app))
                              in
                           FStar_Syntax_Syntax.Tm_meta uu____1928  in
                         FStar_Syntax_Syntax.mk uu____1927  in
                       uu____1924 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1952 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1963 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1974 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1952, uu____1963, uu____1974, env2, e, guard,
                       (let uu___109_1996 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___109_1996.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____2080  ->
                       match uu____2080 with
                       | (p2,imp) ->
                           let uu____2099 = elaborate_pat env1 p2  in
                           (uu____2099, imp)) pats
                   in
                let uu____2104 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2104 with
                 | (uu____2111,t) ->
                     let uu____2113 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2113 with
                      | (f,uu____2129) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2251::uu____2252) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments")
                                  (FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | (uu____2303::uu____2304,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2382  ->
                                        match uu____2382 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2409 =
                                                     let uu____2412 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2412
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2409
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2414 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2414, true)
                                             | uu____2419 ->
                                                 let uu____2422 =
                                                   let uu____2427 =
                                                     let uu____2428 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2428
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2427)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2422
                                                   (FStar_Ident.range_of_lid
                                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2502,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2503)) when p_imp ->
                                     let uu____2506 = aux formals' pats'  in
                                     (p2, true) :: uu____2506
                                 | (uu____2523,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       maybe_dot inaccessible a
                                         (FStar_Ident.range_of_lid
                                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                        in
                                     let uu____2531 = aux formals' pats2  in
                                     (p3, true) :: uu____2531
                                 | (uu____2548,imp) ->
                                     let uu____2554 =
                                       let uu____2561 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2561)  in
                                     let uu____2564 = aux formals' pats'  in
                                     uu____2554 :: uu____2564)
                             in
                          let uu___110_2579 = p1  in
                          let uu____2582 =
                            let uu____2583 =
                              let uu____2596 = aux f pats1  in
                              (fv, uu____2596)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2583  in
                          {
                            FStar_Syntax_Syntax.v = uu____2582;
                            FStar_Syntax_Syntax.p =
                              (uu___110_2579.FStar_Syntax_Syntax.p)
                          }))
            | uu____2613 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2649 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2649 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2707 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2707 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2733 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2733
                       p3.FStar_Syntax_Syntax.p
                 | uu____2756 -> (b, a, w, arg, guard, p3))
             in
          let uu____2765 = one_pat true env p  in
          match uu____2765 with
          | (b,uu____2795,uu____2796,tm,guard,p1) -> (b, tm, guard, p1)
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2842,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2844)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2849,uu____2850) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2854 =
                    let uu____2855 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2856 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2855 uu____2856
                     in
                  failwith uu____2854)
               else ();
               (let uu____2859 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2859
                then
                  let uu____2860 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2861 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2860
                    uu____2861
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___111_2865 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___111_2865.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___111_2865.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2869 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2869
                then
                  let uu____2870 =
                    let uu____2871 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2872 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2871 uu____2872
                     in
                  failwith uu____2870
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___112_2876 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___112_2876.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___112_2876.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2878),uu____2879) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2901 =
                  let uu____2902 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2902  in
                if uu____2901
                then
                  let uu____2903 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2903
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2922;
                FStar_Syntax_Syntax.vars = uu____2923;_},args))
              ->
              ((let uu____2962 =
                  let uu____2963 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2963 Prims.op_Negation  in
                if uu____2962
                then
                  let uu____2964 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2964
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3100)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3175) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3212) ->
                           let pat =
                             let uu____3234 = aux argpat e2  in
                             let uu____3235 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3234, uu____3235)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3240 ->
                      let uu____3263 =
                        let uu____3264 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3265 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3264 uu____3265
                         in
                      failwith uu____3263
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3277;
                     FStar_Syntax_Syntax.vars = uu____3278;_},uu____3279);
                FStar_Syntax_Syntax.pos = uu____3280;
                FStar_Syntax_Syntax.vars = uu____3281;_},args))
              ->
              ((let uu____3324 =
                  let uu____3325 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3325 Prims.op_Negation  in
                if uu____3324
                then
                  let uu____3326 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3326
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3462)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3537) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3574) ->
                           let pat =
                             let uu____3596 = aux argpat e2  in
                             let uu____3597 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3596, uu____3597)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3602 ->
                      let uu____3625 =
                        let uu____3626 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3627 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3626 uu____3627
                         in
                      failwith uu____3625
                   in
                match_args [] args argpats))
          | uu____3636 ->
              let uu____3641 =
                let uu____3642 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3643 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3644 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3642 uu____3643 uu____3644
                 in
              failwith uu____3641
           in
        aux p exp
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____3681 =
      match uu____3681 with
      | (p,i) ->
          let uu____3698 = decorated_pattern_as_term p  in
          (match uu____3698 with
           | (vars,te) ->
               let uu____3721 =
                 let uu____3726 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3726)  in
               (vars, uu____3721))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3740 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3740)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3744 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3744)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3748 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3748)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3769 =
          let uu____3784 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3784 FStar_List.unzip  in
        (match uu____3769 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3894 =
               let uu____3895 =
                 let uu____3896 =
                   let uu____3911 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3911, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3896  in
               mk1 uu____3895  in
             (vars1, uu____3894))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3941,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3951,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3965 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3989)::[] -> wp
      | uu____4006 ->
          let uu____4015 =
            let uu____4016 =
              let uu____4017 =
                FStar_List.map
                  (fun uu____4027  ->
                     match uu____4027 with
                     | (x,uu____4033) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4017 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4016
             in
          failwith uu____4015
       in
    let uu____4038 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4038, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4052 = destruct_comp c  in
        match uu____4052 with
        | (u,uu____4060,wp) ->
            let uu____4062 =
              let uu____4071 =
                let uu____4072 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4072  in
              [uu____4071]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4062;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4082 =
          let uu____4089 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4090 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4089 uu____4090  in
        match uu____4082 with | (m,uu____4092,uu____4093) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4103 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4103
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____4140 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4140 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4177 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4177 with
             | (a,kwp) ->
                 let uu____4208 = destruct_comp m1  in
                 let uu____4215 = destruct_comp m2  in
                 ((md, a, kwp), uu____4208, uu____4215))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____4277 =
              let uu____4278 =
                let uu____4287 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4287]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4278;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4277
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
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
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____4326 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4326
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4329  ->
           let uu____4330 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4330)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4334 =
      let uu____4335 = FStar_Syntax_Subst.compress t  in
      uu____4335.FStar_Syntax_Syntax.n  in
    match uu____4334 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4338 -> true
    | uu____4351 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4389 =
                let uu____4390 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4390  in
              if uu____4389
              then f
              else (let uu____4392 = reason1 ()  in label uu____4392 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___113_4403 = g  in
            let uu____4404 =
              let uu____4405 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4405  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4404;
              FStar_TypeChecker_Env.deferred =
                (uu___113_4403.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___113_4403.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___113_4403.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4419 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4419
        then c
        else
          (let uu____4421 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4421
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4460 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4460]  in
                       let us =
                         let uu____4464 =
                           let uu____4467 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4467]  in
                         u_res :: uu____4464  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4471 =
                         let uu____4472 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4473 =
                           let uu____4474 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4475 =
                             let uu____4478 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4479 =
                               let uu____4482 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4482]  in
                             uu____4478 :: uu____4479  in
                           uu____4474 :: uu____4475  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4472 uu____4473
                          in
                       uu____4471 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4486 = destruct_comp c1  in
              match uu____4486 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____4513  ->
             let uu____4514 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4514)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___81_4521  ->
            match uu___81_4521 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4522 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____4538 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4538))
               &&
               (let uu____4545 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4545 with
                | (head1,uu____4559) ->
                    let uu____4576 =
                      let uu____4577 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4577.FStar_Syntax_Syntax.n  in
                    (match uu____4576 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4581 =
                           let uu____4582 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4582
                            in
                         Prims.op_Negation uu____4581
                     | uu____4583 -> true)))
              &&
              (let uu____4585 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4585)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____4603 =
              let uu____4604 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4604  in
            if uu____4603
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4606 = FStar_Syntax_Util.is_unit t  in
               if uu____4606
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____4612 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4612
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4614 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4614 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4622 =
                             let uu____4623 =
                               let uu____4624 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4625 =
                                 let uu____4626 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4627 =
                                   let uu____4630 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4630]  in
                                 uu____4626 :: uu____4627  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4624
                                 uu____4625
                                in
                             uu____4623 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4622)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4634 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4634
           then
             let uu____4635 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4636 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4637 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4635 uu____4636 uu____4637
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4648 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___82_4652  ->
              match uu___82_4652 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4653 -> false))
       in
    if uu____4648
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___83_4662  ->
              match uu___83_4662 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4675 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4675
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4678 = destruct_comp c1  in
           match uu____4678 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4692 =
                   let uu____4693 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4694 =
                     let uu____4695 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4696 =
                       let uu____4699 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4700 =
                         let uu____4703 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4703]  in
                       uu____4699 :: uu____4700  in
                     uu____4695 :: uu____4696  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4693 uu____4694  in
                 uu____4692 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4706 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4706)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4721 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4723 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4723
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4726 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4726 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____4759 = destruct_comp c1  in
               match uu____4759 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____4773 =
                       let uu____4774 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____4775 =
                         let uu____4776 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____4777 =
                           let uu____4780 =
                             let uu____4781 =
                               let uu____4782 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____4782 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____4781
                              in
                           let uu____4783 =
                             let uu____4786 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____4786]  in
                           uu____4780 :: uu____4783  in
                         uu____4776 :: uu____4777  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4774 uu____4775
                        in
                     uu____4773 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____4821 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____4821
            then (lc, g0)
            else
              (let flags1 =
                 let uu____4830 =
                   let uu____4837 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____4837
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4830 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____4857 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___84_4865  ->
                               match uu___84_4865 with
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
                               | uu____4868 -> []))
                        in
                     FStar_List.append flags1 uu____4857
                  in
               let strengthen uu____4872 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____4876 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____4876 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____4879 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4879
                          then
                            let uu____4880 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____4881 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____4880 uu____4881
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____4883 =
                 let uu____4884 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____4884
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____4883,
                 (let uu___114_4886 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___114_4886.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___114_4886.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___114_4886.FStar_TypeChecker_Env.implicits)
                  })))
  
let (stable_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Syntax_Util.is_tac_lcomp lc)
  
let (stable_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Syntax_Util.is_tot_or_gtot_comp c) ||
      (FStar_Syntax_Util.is_tac_comp c)
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (stable_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___85_4901  ->
            match uu___85_4901 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4902 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____4919 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4919
          then e
          else
            (let uu____4921 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4923 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4923)
                in
             if uu____4921
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____4961  ->
            match uu____4961 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4979 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4979 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4987 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4987
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4994 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____4994
                       then
                         let uu____4997 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____4997
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5001 = stable_lcomp lc21  in
                             if uu____5001
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5006 =
                            (stable_lcomp lc11) && (stable_lcomp lc21)  in
                          if uu____5006
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5010 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5010
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5017 =
                  let uu____5018 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5018
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____5032  ->
                          let uu____5033 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5034 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5036 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5033 uu____5034 uu____5036);
                     (let aux uu____5048 =
                        let uu____5049 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5049
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5070 ->
                              let uu____5071 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5071
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5090 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5090
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5157 =
                              let uu____5162 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5162, reason)  in
                            FStar_Util.Inl uu____5157
                        | uu____5169 -> aux ()  in
                      let try_simplify uu____5191 =
                        let rec maybe_close t x c =
                          let uu____5202 =
                            let uu____5203 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5203.FStar_Syntax_Syntax.n  in
                          match uu____5202 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5207) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5213 -> c  in
                        let uu____5214 =
                          let uu____5215 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5215  in
                        if uu____5214
                        then
                          let uu____5226 =
                            (stable_comp c1) && (stable_comp c2)  in
                          (if uu____5226
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5240 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5240))
                        else
                          (let uu____5250 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5250
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5260 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5260
                              then
                                let uu____5269 =
                                  let uu____5274 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5274, "both gtot")  in
                                FStar_Util.Inl uu____5269
                              else
                                (let uu____5280 =
                                   (stable_comp c1) && (stable_comp c2)  in
                                 if uu____5280
                                 then
                                   let ty = FStar_Syntax_Util.comp_result c2
                                      in
                                   let uu____5292 =
                                     let uu____5297 =
                                       let uu____5298 =
                                         let uu____5299 =
                                           let uu____5300 =
                                             env.FStar_TypeChecker_Env.universe_of
                                               env ty
                                              in
                                           [uu____5300]  in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             uu____5299;
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Tac_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             ty;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags =
                                             [FStar_Syntax_Syntax.SOMETRIVIAL;
                                             FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____5298
                                        in
                                     (uu____5297, "both Tac")  in
                                   FStar_Util.Inl uu____5292
                                 else
                                   (match (e1opt, b) with
                                    | (FStar_Pervasives_Native.Some
                                       e,FStar_Pervasives_Native.Some x) ->
                                        let uu____5330 =
                                          (FStar_Syntax_Util.is_total_comp c1)
                                            &&
                                            (let uu____5332 =
                                               FStar_Syntax_Syntax.is_null_bv
                                                 x
                                                in
                                             Prims.op_Negation uu____5332)
                                           in
                                        if uu____5330
                                        then
                                          let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e)]
                                              c2
                                             in
                                          let x1 =
                                            let uu___115_5343 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_5343.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_5343.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                            }  in
                                          let uu____5344 =
                                            let uu____5349 =
                                              maybe_close
                                                x1.FStar_Syntax_Syntax.sort
                                                x1 c21
                                               in
                                            (uu____5349, "c1 Tot")  in
                                          FStar_Util.Inl uu____5344
                                        else aux ()
                                    | uu____5355 -> aux ()))))
                         in
                      let uu____5364 = try_simplify ()  in
                      match uu____5364 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5384  ->
                                let uu____5385 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5385);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5394  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5409 = lift_and_destruct env c11 c21
                                 in
                              match uu____5409 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5466 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5466]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5468 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5468]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____5481 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5482 =
                                      let uu____5485 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5486 =
                                        let uu____5489 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5490 =
                                          let uu____5493 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5494 =
                                            let uu____5497 =
                                              let uu____5498 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5498
                                               in
                                            [uu____5497]  in
                                          uu____5493 :: uu____5494  in
                                        uu____5489 :: uu____5490  in
                                      uu____5485 :: uu____5486  in
                                    uu____5481 :: uu____5482  in
                                  let wp =
                                    let uu____5502 =
                                      let uu____5503 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5503 wp_args
                                       in
                                    uu____5502 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____5522 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5522 with
                              | (m,uu____5530,lift2) ->
                                  let c23 =
                                    let uu____5533 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5533
                                     in
                                  let uu____5534 = destruct_comp c12  in
                                  (match uu____5534 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5548 =
                                           let uu____5549 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____5550 =
                                             let uu____5551 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____5552 =
                                               let uu____5555 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____5555]  in
                                             uu____5551 :: uu____5552  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5549 uu____5550
                                            in
                                         uu____5548
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____5561 = destruct_comp c1_typ  in
                            match uu____5561 with
                            | (u_res_t1,res_t1,uu____5570) ->
                                let uu____5571 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____5571
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____5574 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____5574
                                   then
                                     (debug1
                                        (fun uu____5582  ->
                                           let uu____5583 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____5584 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5583 uu____5584);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5587 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5589 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____5589)
                                         in
                                      if uu____5587
                                      then
                                        let e1' =
                                          let uu____5611 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____5611
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____5622  ->
                                              let uu____5623 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____5624 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5623 uu____5624);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5636  ->
                                              let uu____5637 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5638 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5637 uu____5638);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____5641 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5641
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____5653 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
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
            (let uu____5669 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____5669)
           in
        let flags1 =
          if should_return1
          then
            let uu____5675 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____5675
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____5683 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____5687 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____5687
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____5689 =
              let uu____5690 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____5690  in
            (if uu____5689
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___116_5693 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___116_5693.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___116_5693.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___116_5693.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____5704 =
                 let uu____5707 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____5707
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5704
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____5712 =
               let uu____5713 =
                 let uu____5714 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5714
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____5713  in
             FStar_Syntax_Util.comp_set_flags uu____5712 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____5737  ->
              match uu____5737 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____5749 =
                      ((let uu____5752 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5752) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5749
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5762 =
        let uu____5763 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5763  in
      FStar_Syntax_Syntax.fvar uu____5762 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5822  ->
                 match uu____5822 with
                 | (uu____5835,eff_label,uu____5837,uu____5838) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____5847 =
          let uu____5854 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5886  ->
                    match uu____5886 with
                    | (uu____5899,uu____5900,flags1,uu____5902) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___86_5914  ->
                                match uu___86_5914 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5915 -> false))))
             in
          if uu____5854
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____5847 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5936 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____5938 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5938
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5958 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____5959 =
                     let uu____5960 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____5961 =
                       let uu____5962 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____5963 =
                         let uu____5966 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____5967 =
                           let uu____5970 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____5971 =
                             let uu____5974 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____5974]  in
                           uu____5970 :: uu____5971  in
                         uu____5966 :: uu____5967  in
                       uu____5962 :: uu____5963  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5960 uu____5961  in
                   uu____5959 FStar_Pervasives_Native.None uu____5958  in
                 let default_case =
                   let post_k =
                     let uu____5981 =
                       let uu____5988 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____5988]  in
                     let uu____5989 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5981 uu____5989  in
                   let kwp =
                     let uu____5995 =
                       let uu____6002 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6002]  in
                     let uu____6003 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5995 uu____6003  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6008 =
                       let uu____6009 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6009]  in
                     let uu____6010 =
                       let uu____6011 =
                         let uu____6014 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6014
                          in
                       let uu____6015 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6011 uu____6015  in
                     FStar_Syntax_Util.abs uu____6008 uu____6010
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____6031 =
                     should_not_inline_whole_match ||
                       (let uu____6033 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6033)
                      in
                   if uu____6031 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6065  ->
                        fun celse  ->
                          match uu____6065 with
                          | (g,eff_label,uu____6081,cthen) ->
                              let uu____6091 =
                                let uu____6116 =
                                  let uu____6117 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6117
                                   in
                                lift_and_destruct env uu____6116 celse  in
                              (match uu____6091 with
                               | ((md,uu____6119,uu____6120),(uu____6121,uu____6122,wp_then),
                                  (uu____6124,uu____6125,wp_else)) ->
                                   let uu____6145 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6145 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6158::[] -> comp
                 | uu____6195 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6212 = destruct_comp comp1  in
                     (match uu____6212 with
                      | (uu____6219,uu____6220,wp) ->
                          let wp1 =
                            let uu____6225 =
                              let uu____6226 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6227 =
                                let uu____6228 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6229 =
                                  let uu____6232 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6232]  in
                                uu____6228 :: uu____6229  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6226
                                uu____6227
                               in
                            uu____6225 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____6259 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6259 with
          | FStar_Pervasives_Native.None  ->
              let uu____6268 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6273 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6268 uu____6273
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
            let uu____6306 =
              let uu____6307 = FStar_Syntax_Subst.compress t2  in
              uu____6307.FStar_Syntax_Syntax.n  in
            match uu____6306 with
            | FStar_Syntax_Syntax.Tm_type uu____6310 -> true
            | uu____6311 -> false  in
          let uu____6312 =
            let uu____6313 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6313.FStar_Syntax_Syntax.n  in
          match uu____6312 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6321 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6332 =
                  let uu____6333 =
                    let uu____6334 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6334
                     in
                  (FStar_Pervasives_Native.None, uu____6333)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6332
                 in
              let e1 =
                let uu____6344 =
                  let uu____6345 =
                    let uu____6346 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6346]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6345  in
                uu____6344 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6351 -> (e, lc)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____6380 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6380 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6403 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6425 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6425, false)
            else
              (let uu____6431 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6431, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6442) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6451 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6451 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___117_6465 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___117_6465.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___117_6465.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___117_6465.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6470 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6470 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___118_6478 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___118_6478.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___118_6478.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___118_6478.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___119_6481 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_6481.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_6481.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___119_6481.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6485 =
                     let uu____6486 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6486
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6489 =
                          let uu____6490 = FStar_Syntax_Subst.compress f1  in
                          uu____6490.FStar_Syntax_Syntax.n  in
                        match uu____6489 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6493,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6495;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6496;_},uu____6497)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___120_6519 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___120_6519.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___120_6519.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___120_6519.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6520 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____6523 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6523
                              then
                                let uu____6524 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6525 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6526 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6527 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6524 uu____6525 uu____6526 uu____6527
                              else ());
                             (let u_t_opt = comp_univ_opt c  in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let cret = return_value env u_t_opt t xexp  in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____6540 =
                                    let uu____6541 =
                                      let uu____6542 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____6542]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6541
                                     in
                                  uu____6540 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____6546 =
                                let uu____6551 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____6564 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____6565 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____6566 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____6551 uu____6564
                                  e uu____6565 uu____6566
                                 in
                              match uu____6546 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___121_6570 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_6570.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_6570.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____6572 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____6572
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____6577 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____6577
                                    then
                                      let uu____6578 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6578
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___87_6588  ->
                             match uu___87_6588 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6591 -> []))
                      in
                   let lc1 =
                     let uu____6593 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____6593 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___122_6595 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_6595.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_6595.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___122_6595.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____6618 =
          let uu____6619 =
            let uu____6620 =
              let uu____6621 =
                let uu____6622 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____6622  in
              [uu____6621]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6620  in
          uu____6619 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____6618  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____6629 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____6629
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6647 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6662 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6691)::(ens,uu____6693)::uu____6694 ->
                    let uu____6723 =
                      let uu____6726 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____6726  in
                    let uu____6727 =
                      let uu____6728 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____6728  in
                    (uu____6723, uu____6727)
                | uu____6731 ->
                    let uu____6740 =
                      let uu____6745 =
                        let uu____6746 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6746
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6745)
                       in
                    FStar_Errors.raise_error uu____6740
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6762)::uu____6763 ->
                    let uu____6782 =
                      let uu____6787 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6787
                       in
                    (match uu____6782 with
                     | (us_r,uu____6819) ->
                         let uu____6820 =
                           let uu____6825 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6825
                            in
                         (match uu____6820 with
                          | (us_e,uu____6857) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____6860 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6860
                                  us_r
                                 in
                              let as_ens =
                                let uu____6862 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6862
                                  us_e
                                 in
                              let req =
                                let uu____6866 =
                                  let uu____6867 =
                                    let uu____6868 =
                                      let uu____6879 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6879]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6868
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6867
                                   in
                                uu____6866 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____6897 =
                                  let uu____6898 =
                                    let uu____6899 =
                                      let uu____6910 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6910]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6899
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6898
                                   in
                                uu____6897 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6925 =
                                let uu____6928 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6928  in
                              let uu____6929 =
                                let uu____6930 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6930  in
                              (uu____6925, uu____6929)))
                | uu____6933 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____6959 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6959
       then
         let uu____6960 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6961 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6960 uu____6961
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____6979 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6979
         then
           let uu____6980 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6981 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6980
             uu____6981
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6986 =
      let uu____6987 =
        let uu____6988 = FStar_Syntax_Subst.compress t  in
        uu____6988.FStar_Syntax_Syntax.n  in
      match uu____6987 with
      | FStar_Syntax_Syntax.Tm_app uu____6991 -> false
      | uu____7006 -> true  in
    if uu____6986
    then t
    else
      (let uu____7008 = FStar_Syntax_Util.head_and_args t  in
       match uu____7008 with
       | (head1,args) ->
           let uu____7045 =
             let uu____7046 =
               let uu____7047 = FStar_Syntax_Subst.compress head1  in
               uu____7047.FStar_Syntax_Syntax.n  in
             match uu____7046 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7050 -> false  in
           if uu____7045
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7072 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____7109 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7109 with
             | (formals,uu____7123) ->
                 let n_implicits =
                   let uu____7141 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7217  ->
                             match uu____7217 with
                             | (uu____7224,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7141 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7355 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7355 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7379 =
                     let uu____7384 =
                       let uu____7385 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7392 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7393 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7385 uu____7392 uu____7393
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7384)
                      in
                   let uu____7400 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7379 uu____7400
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___88_7421 =
             match uu___88_7421 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7451 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7451 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7560) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7603,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____7636 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____7636 with
                           | (v1,uu____7676,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____7693 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____7693 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7786 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7786)))
                      | (uu____7813,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____7859 =
                      let uu____7886 = inst_n_binders t  in
                      aux [] uu____7886 bs1  in
                    (match uu____7859 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7957) -> (e, torig, guard)
                          | (uu____7988,[]) when
                              let uu____8019 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8019 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8020 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8052 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8067 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8075 =
      let uu____8078 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8078
        (FStar_List.map
           (fun u  ->
              let uu____8088 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8088 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8075 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8105 = FStar_Util.set_is_empty x  in
      if uu____8105
      then []
      else
        (let s =
           let uu____8112 =
             let uu____8115 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8115  in
           FStar_All.pipe_right uu____8112 FStar_Util.set_elements  in
         (let uu____8123 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____8123
          then
            let uu____8124 =
              let uu____8125 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____8125  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8124
          else ());
         (let r =
            let uu____8132 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____8132  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____8147 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8147
                     then
                       let uu____8148 =
                         let uu____8149 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8149
                          in
                       let uu____8150 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8151 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8148 uu____8150 uu____8151
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____8173 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____8173 FStar_Util.fifo_set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____8205) -> generalized_univ_names
        | (uu____8212,[]) -> explicit_univ_names
        | uu____8219 ->
            let uu____8228 =
              let uu____8233 =
                let uu____8234 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8234
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8233)
               in
            FStar_Errors.raise_error uu____8228 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      let univs1 = FStar_Syntax_Free.univs t  in
      (let uu____8251 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____8251
       then
         let uu____8252 = string_of_univs univs1  in
         FStar_Util.print1 "univs to gen : %s\n" uu____8252
       else ());
      (let gen1 = gen_univs env univs1  in
       (let uu____8258 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8258
        then
          let uu____8259 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "After generalization: %s\n" uu____8259
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0  in
        let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
        (univs2, ts)))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____8329 =
          let uu____8330 =
            FStar_Util.for_all
              (fun uu____8343  ->
                 match uu____8343 with
                 | (uu____8352,uu____8353,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8330  in
        if uu____8329
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8399 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8399
              then
                let uu____8400 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8400
              else ());
             (let c1 =
                let uu____8403 = FStar_TypeChecker_Env.should_verify env  in
                if uu____8403
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
                    FStar_TypeChecker_Normalize.NoFullNorm] env c
                 in
              (let uu____8406 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8406
               then
                 let uu____8407 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8407
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8468 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8468 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8598 =
             match uu____8598 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____8664 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8664
                   then
                     let uu____8665 =
                       let uu____8666 =
                         let uu____8669 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8669
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8666
                         (FStar_String.concat ", ")
                        in
                     let uu____8696 =
                       let uu____8697 =
                         let uu____8700 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8700
                           (FStar_List.map
                              (fun uu____8728  ->
                                 match uu____8728 with
                                 | (u,t2) ->
                                     let uu____8735 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____8736 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8735 uu____8736))
                          in
                       FStar_All.pipe_right uu____8697
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8665
                       uu____8696
                   else ());
                  (let univs2 =
                     let uu____8743 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8766  ->
                            match uu____8766 with
                            | (uu____8775,t2) ->
                                let uu____8777 = FStar_Syntax_Free.univs t2
                                   in
                                FStar_Util.set_union univs2 uu____8777)
                       univs1 uu____8743
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8800 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8800
                    then
                      let uu____8801 =
                        let uu____8802 =
                          let uu____8805 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8805
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8802
                          (FStar_String.concat ", ")
                         in
                      let uu____8832 =
                        let uu____8833 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8865  ->
                                  match uu____8865 with
                                  | (u,t2) ->
                                      let uu____8872 =
                                        FStar_Syntax_Print.uvar_to_string u
                                         in
                                      let uu____8873 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2
                                         in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8872 uu____8873))
                           in
                        FStar_All.pipe_right uu____8833
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8801
                        uu____8832
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8903 =
             let uu____8936 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8936  in
           match uu____8903 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9054 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9054
                 then ()
                 else
                   (let uu____9056 = lec_hd  in
                    match uu____9056 with
                    | (lb1,uu____9064,uu____9065) ->
                        let uu____9066 = lec2  in
                        (match uu____9066 with
                         | (lb2,uu____9074,uu____9075) ->
                             let msg =
                               let uu____9077 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9078 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9077 uu____9078
                                in
                             let uu____9079 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9079))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9190  ->
                           match uu____9190 with
                           | (u,uu____9198) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9220  ->
                                       match uu____9220 with
                                       | (u',uu____9228) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9233 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9233
                 then ()
                 else
                   (let uu____9235 = lec_hd  in
                    match uu____9235 with
                    | (lb1,uu____9243,uu____9244) ->
                        let uu____9245 = lec2  in
                        (match uu____9245 with
                         | (lb2,uu____9253,uu____9254) ->
                             let msg =
                               let uu____9256 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9257 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9256 uu____9257
                                in
                             let uu____9258 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9258))
                  in
               let lecs1 =
                 let uu____9268 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9327 = univs_and_uvars_of_lec this_lec  in
                        match uu____9327 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9268 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail k =
                   let uu____9480 = lec_hd  in
                   match uu____9480 with
                   | (lbname,e,c) ->
                       let uu____9490 =
                         let uu____9495 =
                           let uu____9496 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____9497 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____9498 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9496 uu____9497 uu____9498
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9495)
                          in
                       let uu____9499 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9490 uu____9499
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9529  ->
                         match uu____9529 with
                         | (u,k) ->
                             let uu____9542 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____9542 with
                              | FStar_Pervasives_Native.Some uu____9551 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9558 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____9562 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____9562 with
                                   | (bs,kres) ->
                                       ((let uu____9600 =
                                           let uu____9601 =
                                             let uu____9604 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____9604
                                              in
                                           uu____9601.FStar_Syntax_Syntax.n
                                            in
                                         match uu____9600 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9605 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____9609 =
                                               let uu____9610 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____9610
                                                in
                                             if uu____9609
                                             then fail kres
                                             else ()
                                         | uu____9612 -> fail kres);
                                        (let a =
                                           let uu____9614 =
                                             let uu____9617 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9617
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9614 kres
                                            in
                                         let t =
                                           let uu____9621 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Util.abs bs
                                             uu____9621
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.residual_tot
                                                   kres))
                                            in
                                         FStar_Syntax_Util.set_uvar u t;
                                         (a,
                                           (FStar_Pervasives_Native.Some
                                              FStar_Syntax_Syntax.imp_tag))))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9740  ->
                         match uu____9740 with
                         | (lbname,e,c) ->
                             let uu____9786 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9855 ->
                                   let uu____9870 = (e, c)  in
                                   (match uu____9870 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____9907  ->
                                                   match uu____9907 with
                                                   | (x,uu____9915) ->
                                                       let uu____9920 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9920)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9930 =
                                                let uu____9931 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9931
                                                 in
                                              if uu____9930
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____9939 =
                                            let uu____9940 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9940.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9939 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9963 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9963 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9978 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9980 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9980, gen_tvars))
                                in
                             (match uu____9786 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____10126 = Obj.magic ()  in ());
        (let uu____10128 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10128
         then
           let uu____10129 =
             let uu____10130 =
               FStar_List.map
                 (fun uu____10143  ->
                    match uu____10143 with
                    | (lb,uu____10151,uu____10152) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10130 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10129
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10173  ->
                match uu____10173 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10202 = gen env is_rec lecs  in
           match uu____10202 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10301  ->
                       match uu____10301 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10363 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10363
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10407  ->
                           match uu____10407 with
                           | (l,us,e,c,gvs) ->
                               let uu____10441 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____10442 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____10443 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____10444 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____10445 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10441 uu____10442 uu____10443
                                 uu____10444 uu____10445))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10486  ->
                match uu____10486 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10530 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____10530, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____10573 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____10573 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10579 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10579)
             in
          let is_var e1 =
            let uu____10586 =
              let uu____10587 = FStar_Syntax_Subst.compress e1  in
              uu____10587.FStar_Syntax_Syntax.n  in
            match uu____10586 with
            | FStar_Syntax_Syntax.Tm_name uu____10590 -> true
            | uu____10591 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___123_10607 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___123_10607.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___123_10607.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10608 -> e2  in
          let env2 =
            let uu___124_10610 = env1  in
            let uu____10611 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___124_10610.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___124_10610.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___124_10610.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___124_10610.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___124_10610.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___124_10610.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___124_10610.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___124_10610.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___124_10610.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___124_10610.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___124_10610.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___124_10610.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___124_10610.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___124_10610.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___124_10610.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10611;
              FStar_TypeChecker_Env.is_iface =
                (uu___124_10610.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___124_10610.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___124_10610.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___124_10610.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___124_10610.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___124_10610.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___124_10610.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___124_10610.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___124_10610.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___124_10610.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___124_10610.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___124_10610.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___124_10610.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___124_10610.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___124_10610.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___124_10610.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___124_10610.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___124_10610.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___124_10610.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____10612 = check env2 t1 t2  in
          match uu____10612 with
          | FStar_Pervasives_Native.None  ->
              let uu____10619 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____10624 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____10619 uu____10624
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10631 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10631
                then
                  let uu____10632 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10632
                else ());
               (let uu____10634 = decorate e t2  in (uu____10634, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____10662 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____10662
        then
          let uu____10667 = discharge g1  in
          let uu____10668 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____10667, uu____10668)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps = [FStar_TypeChecker_Normalize.Beta]  in
           let c1 =
             let uu____10675 =
               let uu____10676 =
                 let uu____10677 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____10677 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____10676
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____10675
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____10679 = destruct_comp c1  in
           match uu____10679 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10696 = FStar_TypeChecker_Env.get_range env  in
                 let uu____10697 =
                   let uu____10698 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____10699 =
                     let uu____10700 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____10701 =
                       let uu____10704 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____10704]  in
                     uu____10700 :: uu____10701  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10698 uu____10699  in
                 uu____10697 FStar_Pervasives_Native.None uu____10696  in
               ((let uu____10708 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____10708
                 then
                   let uu____10709 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10709
                 else ());
                (let g2 =
                   let uu____10712 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10712  in
                 let uu____10713 = discharge g2  in
                 let uu____10714 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____10713, uu____10714))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___89_10738 =
        match uu___89_10738 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10746)::[] -> f fst1
        | uu____10763 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10768 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10768
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44)
         in
      let op_or_e e =
        let uu____10777 =
          let uu____10780 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10780  in
        FStar_All.pipe_right uu____10777
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46)
         in
      let op_or_t t =
        let uu____10791 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10791
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
         in
      let short_op_ite uu___90_10805 =
        match uu___90_10805 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10813)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10832)::[] ->
            let uu____10861 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10861
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10866 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10876 =
          let uu____10883 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10883)  in
        let uu____10888 =
          let uu____10897 =
            let uu____10904 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10904)  in
          let uu____10909 =
            let uu____10918 =
              let uu____10925 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10925)  in
            let uu____10930 =
              let uu____10939 =
                let uu____10946 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10946)  in
              let uu____10951 =
                let uu____10960 =
                  let uu____10967 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10967)  in
                [uu____10960; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10939 :: uu____10951  in
            uu____10918 :: uu____10930  in
          uu____10897 :: uu____10909  in
        uu____10876 :: uu____10888  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11018 =
            FStar_Util.find_map table
              (fun uu____11031  ->
                 match uu____11031 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11048 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11048
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11018 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11051 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11055 =
      let uu____11056 = FStar_Syntax_Util.un_uinst l  in
      uu____11056.FStar_Syntax_Syntax.n  in
    match uu____11055 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11060 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11084)::uu____11085 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11096 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11103,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11104))::uu____11105 -> bs
      | uu____11122 ->
          let uu____11123 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11123 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11127 =
                 let uu____11128 = FStar_Syntax_Subst.compress t  in
                 uu____11128.FStar_Syntax_Syntax.n  in
               (match uu____11127 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11132) ->
                    let uu____11149 =
                      FStar_Util.prefix_until
                        (fun uu___91_11189  ->
                           match uu___91_11189 with
                           | (uu____11196,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11197)) ->
                               false
                           | uu____11200 -> true) bs'
                       in
                    (match uu____11149 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11235,uu____11236) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11308,uu____11309) ->
                         let uu____11382 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11400  ->
                                   match uu____11400 with
                                   | (x,uu____11408) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____11382
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11455  ->
                                     match uu____11455 with
                                     | (x,i) ->
                                         let uu____11474 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11474, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11484 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
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
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____11516 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11516
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____11539 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11539
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11541 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11541))
         else ());
        (let fv =
           let uu____11544 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11544
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def;
                FStar_Syntax_Syntax.lbattrs = []
              }])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____11554 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___125_11560 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___125_11560.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___125_11560.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___125_11560.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___125_11560.FStar_Syntax_Syntax.sigattrs)
           }), uu____11554))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      let visibility uu___92_11570 =
        match uu___92_11570 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11571 -> false  in
      let reducibility uu___93_11575 =
        match uu___93_11575 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11576 -> false  in
      let assumption uu___94_11580 =
        match uu___94_11580 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11581 -> false  in
      let reification uu___95_11585 =
        match uu___95_11585 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11586 -> true
        | uu____11587 -> false  in
      let inferred uu___96_11591 =
        match uu___96_11591 with
        | FStar_Syntax_Syntax.Discriminator uu____11592 -> true
        | FStar_Syntax_Syntax.Projector uu____11593 -> true
        | FStar_Syntax_Syntax.RecordType uu____11598 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11607 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11616 -> false  in
      let has_eq uu___97_11620 =
        match uu___97_11620 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11621 -> false  in
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
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
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
        | FStar_Syntax_Syntax.Reflectable uu____11681 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11686 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____11690 =
        let uu____11691 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___98_11695  ->
                  match uu___98_11695 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11696 -> false))
           in
        FStar_All.pipe_right uu____11691 Prims.op_Negation  in
      if uu____11690
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11709 =
            let uu____11714 =
              let uu____11715 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11715 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11714)  in
          FStar_Errors.raise_error uu____11709 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11723 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11727 =
            let uu____11728 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11728  in
          if uu____11727 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11733),uu____11734) ->
              ((let uu____11750 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11750
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11754 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11754
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11760 ->
              let uu____11769 =
                let uu____11770 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____11770  in
              if uu____11769 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11776 ->
              let uu____11783 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11783 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11787 ->
              let uu____11794 =
                let uu____11795 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11795  in
              if uu____11794 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11801 ->
              let uu____11802 =
                let uu____11803 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11803  in
              if uu____11802 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11809 ->
              let uu____11810 =
                let uu____11811 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11811  in
              if uu____11810 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11817 ->
              let uu____11830 =
                let uu____11831 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11831  in
              if uu____11830 then err'1 () else ()
          | uu____11837 -> ()))
      else ()
  
let (mk_discriminator_and_indexed_projectors :
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
                      FStar_Syntax_Syntax.sigelt Prims.list)
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
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____11900 =
                            let uu____11903 =
                              let uu____11904 =
                                let uu____11911 =
                                  let uu____11912 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11912
                                   in
                                (uu____11911, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____11904  in
                            FStar_Syntax_Syntax.mk uu____11903  in
                          uu____11900 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11953  ->
                                  match uu____11953 with
                                  | (x,imp) ->
                                      let uu____11964 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____11964, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____11966 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____11966  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11975 =
                               let uu____11976 =
                                 let uu____11977 =
                                   let uu____11978 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____11979 =
                                     let uu____11980 =
                                       let uu____11981 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11981
                                        in
                                     [uu____11980]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11978
                                     uu____11979
                                    in
                                 uu____11977 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____11976  in
                             FStar_Syntax_Util.refine x uu____11975  in
                           let uu____11984 =
                             let uu___126_11985 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___126_11985.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___126_11985.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____11984)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____12000 =
                          FStar_List.map
                            (fun uu____12022  ->
                               match uu____12022 with
                               | (x,uu____12034) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____12000 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12083  ->
                                match uu____12083 with
                                | (x,uu____12095) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             (let uu____12109 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12109)
                               ||
                               (let uu____12111 =
                                  let uu____12112 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____12112.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____12111)
                              in
                           let quals =
                             let uu____12116 =
                               let uu____12119 =
                                 let uu____12122 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit)
                                    in
                                 if uu____12122
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else []  in
                               let uu____12126 =
                                 FStar_List.filter
                                   (fun uu___99_12130  ->
                                      match uu___99_12130 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____12131 -> false) iquals
                                  in
                               FStar_List.append uu____12119 uu____12126  in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____12116
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____12152 =
                                 let uu____12153 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12153  in
                               FStar_Syntax_Syntax.mk_Total uu____12152  in
                             let uu____12154 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12154
                              in
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
                             }  in
                           (let uu____12157 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____12157
                            then
                              let uu____12158 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12158
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
                                             fun uu____12211  ->
                                               match uu____12211 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12235 =
                                                       let uu____12238 =
                                                         let uu____12239 =
                                                           let uu____12246 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____12246,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12239
                                                          in
                                                       pos uu____12238  in
                                                     (uu____12235, b)
                                                   else
                                                     (let uu____12250 =
                                                        let uu____12253 =
                                                          let uu____12254 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12254
                                                           in
                                                        pos uu____12253  in
                                                      (uu____12250, b))))
                                      in
                                   let pat_true =
                                     let uu____12272 =
                                       let uu____12275 =
                                         let uu____12276 =
                                           let uu____12289 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____12289, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12276
                                          in
                                       pos uu____12275  in
                                     (uu____12272,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____12323 =
                                       let uu____12326 =
                                         let uu____12327 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12327
                                          in
                                       pos uu____12326  in
                                     (uu____12323,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____12339 =
                                     let uu____12342 =
                                       let uu____12343 =
                                         let uu____12366 =
                                           let uu____12369 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____12370 =
                                             let uu____12373 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____12373]  in
                                           uu____12369 :: uu____12370  in
                                         (arg_exp, uu____12366)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12343
                                        in
                                     FStar_Syntax_Syntax.mk uu____12342  in
                                   uu____12339 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____12380 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____12380
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____12388 =
                                  let uu____12393 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____12393  in
                                let uu____12394 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____12388;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Parser_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____12394;
                                  FStar_Syntax_Syntax.lbattrs = []
                                }  in
                              let impl =
                                let uu____12400 =
                                  let uu____12401 =
                                    let uu____12408 =
                                      let uu____12411 =
                                        let uu____12412 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____12412
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____12411]  in
                                    ((false, [lb]), uu____12408)  in
                                  FStar_Syntax_Syntax.Sig_let uu____12401  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12400;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____12430 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____12430
                               then
                                 let uu____12431 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12431
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____12473  ->
                                  match uu____12473 with
                                  | (a,uu____12479) ->
                                      let uu____12480 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____12480 with
                                       | (field_name,uu____12486) ->
                                           let field_proj_tm =
                                             let uu____12488 =
                                               let uu____12489 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12489
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12488 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____12506 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12538  ->
                                    match uu____12538 with
                                    | (x,uu____12546) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____12548 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____12548 with
                                         | (field_name,uu____12556) ->
                                             let t =
                                               let uu____12558 =
                                                 let uu____12559 =
                                                   let uu____12562 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12562
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12559
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12558
                                                in
                                             let only_decl =
                                               (let uu____12566 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env
                                                   in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12566)
                                                 ||
                                                 (let uu____12568 =
                                                    let uu____12569 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____12569.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12568)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12583 =
                                                   FStar_List.filter
                                                     (fun uu___100_12587  ->
                                                        match uu___100_12587
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12588 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12583
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___101_12601  ->
                                                         match uu___101_12601
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12602 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
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
                                               }  in
                                             ((let uu____12621 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____12621
                                               then
                                                 let uu____12622 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12622
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____12670 
                                                             ->
                                                             match uu____12670
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12694
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____12694,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12710
                                                                    =
                                                                    let uu____12713
                                                                    =
                                                                    let uu____12714
                                                                    =
                                                                    let uu____12721
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____12721,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12714
                                                                     in
                                                                    pos
                                                                    uu____12713
                                                                     in
                                                                    (uu____12710,
                                                                    b))
                                                                   else
                                                                    (let uu____12725
                                                                    =
                                                                    let uu____12728
                                                                    =
                                                                    let uu____12729
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12729
                                                                     in
                                                                    pos
                                                                    uu____12728
                                                                     in
                                                                    (uu____12725,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____12745 =
                                                     let uu____12748 =
                                                       let uu____12749 =
                                                         let uu____12762 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____12762,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12749
                                                        in
                                                     pos uu____12748  in
                                                   let uu____12771 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____12745,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12771)
                                                    in
                                                 let body =
                                                   let uu____12783 =
                                                     let uu____12786 =
                                                       let uu____12787 =
                                                         let uu____12810 =
                                                           let uu____12813 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____12813]  in
                                                         (arg_exp,
                                                           uu____12810)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12787
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12786
                                                      in
                                                   uu____12783
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____12821 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____12821
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____12828 =
                                                     let uu____12833 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____12833
                                                      in
                                                   let uu____12834 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12828;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12834;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = []
                                                   }  in
                                                 let impl =
                                                   let uu____12840 =
                                                     let uu____12841 =
                                                       let uu____12848 =
                                                         let uu____12851 =
                                                           let uu____12852 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____12852
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____12851]  in
                                                       ((false, [lb]),
                                                         uu____12848)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12841
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12840;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____12870 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____12870
                                                  then
                                                    let uu____12871 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12871
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____12506 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12911) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12916 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____12916 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____12938 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____12938 with
                    | (formals,uu____12954) ->
                        let uu____12971 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____13003 =
                                   let uu____13004 =
                                     let uu____13005 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____13005  in
                                   FStar_Ident.lid_equals typ_lid uu____13004
                                    in
                                 if uu____13003
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____13024,uvs',tps,typ0,uu____13028,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____13047 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
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
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____12971 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____13120 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____13120 with
                              | (indices,uu____13136) ->
                                  let refine_domain =
                                    let uu____13154 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___102_13159  ->
                                              match uu___102_13159 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13160 -> true
                                              | uu____13169 -> false))
                                       in
                                    if uu____13154
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___103_13177 =
                                      match uu___103_13177 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13180,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13192 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____13193 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____13193 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____13204 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____13204 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13269  ->
                                               fun uu____13270  ->
                                                 match (uu____13269,
                                                         uu____13270)
                                                 with
                                                 | ((x,uu____13288),(x',uu____13290))
                                                     ->
                                                     let uu____13299 =
                                                       let uu____13306 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____13306)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13299) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13307 -> []
  