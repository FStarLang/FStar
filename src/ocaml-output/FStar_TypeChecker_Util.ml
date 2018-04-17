open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____21 = FStar_TypeChecker_Env.get_range env  in
      let uu____22 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____21 uu____22
  
let (is_type : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____32 =
      let uu____33 = FStar_Syntax_Subst.compress t  in
      uu____33.FStar_Syntax_Syntax.n  in
    match uu____32 with
    | FStar_Syntax_Syntax.Tm_type uu____36 -> true
    | uu____37 -> false
  
let (t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    let uu____49 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____49
      (FStar_List.filter
         (fun uu____63  ->
            match uu____63 with
            | (x,uu____69) -> is_type x.FStar_Syntax_Syntax.sort))
  
let (new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____85 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____87 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____87)
           in
        if uu____85
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____89 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Rel.new_uvar uu____89 bs k
  
let (new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____100 = new_uvar_aux env k  in
      FStar_Pervasives_Native.fst uu____100
  
let (as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar) =
  fun uu___77_112  ->
    match uu___77_112 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____114);
        FStar_Syntax_Syntax.pos = uu____115;
        FStar_Syntax_Syntax.vars = uu____116;_} -> uv
    | uu____143 -> failwith "Impossible"
  
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
          let uu____176 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____176 with
          | FStar_Pervasives_Native.Some (uu____199::(tm,uu____201)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____253 ->
              let uu____264 = new_uvar_aux env k  in
              (match uu____264 with
               | (t,u) ->
                   let g =
                     let uu___96_284 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____285 =
                       let uu____300 =
                         let uu____313 = as_uvar u  in
                         (reason, env, uu____313, t, k, r)  in
                       [uu____300]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___96_284.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___96_284.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___96_284.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____285
                     }  in
                   let uu____338 =
                     let uu____345 =
                       let uu____350 = as_uvar u  in (uu____350, r)  in
                     [uu____345]  in
                   (t, uu____338, g))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____382 =
        let uu____383 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____383  in
      if uu____382
      then
        let us =
          let uu____389 =
            let uu____392 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____410  ->
                 match uu____410 with
                 | (x,uu____416) -> FStar_Syntax_Print.uvar_to_string x)
              uu____392
             in
          FStar_All.pipe_right uu____389 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____423 =
            let uu____428 =
              let uu____429 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____429
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____428)  in
          FStar_Errors.log_issue r uu____423);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____446  ->
      match uu____446 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____456;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____458;
          FStar_Syntax_Syntax.lbpos = uu____459;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____492 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____492 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let mk_binder1 scope a =
                      let uu____524 =
                        let uu____525 =
                          FStar_Syntax_Subst.compress
                            a.FStar_Syntax_Syntax.sort
                           in
                        uu____525.FStar_Syntax_Syntax.n  in
                      match uu____524 with
                      | FStar_Syntax_Syntax.Tm_unknown  ->
                          let uu____532 = FStar_Syntax_Util.type_u ()  in
                          (match uu____532 with
                           | (k,uu____542) ->
                               let t2 =
                                 let uu____544 =
                                   FStar_TypeChecker_Rel.new_uvar
                                     e1.FStar_Syntax_Syntax.pos scope k
                                    in
                                 FStar_All.pipe_right uu____544
                                   FStar_Pervasives_Native.fst
                                  in
                               ((let uu___97_554 = a  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___97_554.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___97_554.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t2
                                 }), false))
                      | uu____555 -> (a, true)  in
                    let rec aux must_check_ty vars e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____598) ->
                          aux must_check_ty vars e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____605) ->
                          ((FStar_Pervasives_Native.fst t2), true)
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____668) ->
                          let uu____689 =
                            FStar_All.pipe_right bs
                              (FStar_List.fold_left
                                 (fun uu____749  ->
                                    fun uu____750  ->
                                      match (uu____749, uu____750) with
                                      | ((scope,bs1,must_check_ty1),(a,imp))
                                          ->
                                          let uu____828 =
                                            if must_check_ty1
                                            then (a, true)
                                            else mk_binder1 scope a  in
                                          (match uu____828 with
                                           | (tb,must_check_ty2) ->
                                               let b = (tb, imp)  in
                                               let bs2 =
                                                 FStar_List.append bs1 [b]
                                                  in
                                               let scope1 =
                                                 FStar_List.append scope [b]
                                                  in
                                               (scope1, bs2, must_check_ty2)))
                                 (vars, [], must_check_ty))
                             in
                          (match uu____689 with
                           | (scope,bs1,must_check_ty1) ->
                               let uu____940 = aux must_check_ty1 scope body
                                  in
                               (match uu____940 with
                                | (res,must_check_ty2) ->
                                    let c =
                                      match res with
                                      | FStar_Util.Inl t2 ->
                                          let uu____969 =
                                            FStar_Options.ml_ish ()  in
                                          if uu____969
                                          then FStar_Syntax_Util.ml_comp t2 r
                                          else
                                            FStar_Syntax_Syntax.mk_Total t2
                                      | FStar_Util.Inr c -> c  in
                                    let t2 = FStar_Syntax_Util.arrow bs1 c
                                       in
                                    ((let uu____976 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.High
                                         in
                                      if uu____976
                                      then
                                        let uu____977 =
                                          FStar_Range.string_of_range r  in
                                        let uu____978 =
                                          FStar_Syntax_Print.term_to_string
                                            t2
                                           in
                                        let uu____979 =
                                          FStar_Util.string_of_bool
                                            must_check_ty2
                                           in
                                        FStar_Util.print3
                                          "(%s) Using type %s .... must check = %s\n"
                                          uu____977 uu____978 uu____979
                                      else ());
                                     ((FStar_Util.Inl t2), must_check_ty2))))
                      | uu____989 ->
                          if must_check_ty
                          then
                            ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                          else
                            (let uu____1003 =
                               let uu____1008 =
                                 let uu____1009 =
                                   FStar_TypeChecker_Rel.new_uvar r vars
                                     FStar_Syntax_Util.ktype0
                                    in
                                 FStar_All.pipe_right uu____1009
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_Util.Inl uu____1008  in
                             (uu____1003, false))
                       in
                    let uu____1022 =
                      let uu____1031 = t_binders env1  in
                      aux false uu____1031 e1  in
                    (match uu____1022 with
                     | (t2,b) ->
                         let t3 =
                           match t2 with
                           | FStar_Util.Inr c ->
                               let uu____1056 =
                                 FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                               if uu____1056
                               then FStar_Syntax_Util.comp_result c
                               else
                                 (let uu____1060 =
                                    let uu____1065 =
                                      let uu____1066 =
                                        FStar_Syntax_Print.comp_to_string c
                                         in
                                      FStar_Util.format1
                                        "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                        uu____1066
                                       in
                                    (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                      uu____1065)
                                     in
                                  FStar_Errors.raise_error uu____1060 rng)
                           | FStar_Util.Inl t3 -> t3  in
                         (univ_vars2, t3, b)))
           | uu____1072 ->
               let uu____1073 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1073 with
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
            let uu____1165 =
              let uu____1170 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1170 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1175;
                  FStar_Syntax_Syntax.vars = uu____1176;_} ->
                  let uu____1179 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1179 with
                   | (t,uu____1189) ->
                       let uu____1190 = new_uvar env1 t  in
                       (uu____1190, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1165 with
            | (t_x,guard) ->
                ((let uu___98_1199 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___98_1199.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___98_1199.FStar_Syntax_Syntax.index);
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
                  | uu____1274 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1282) ->
                let uu____1287 = FStar_Syntax_Util.type_u ()  in
                (match uu____1287 with
                 | (k,uu____1313) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___99_1316 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___99_1316.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___99_1316.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1317 =
                       let uu____1322 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1322 t
                        in
                     (match uu____1317 with
                      | (e,u) ->
                          let p2 =
                            let uu___100_1348 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___100_1348.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1358 = check_bv env1 x  in
                (match uu____1358 with
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
                let uu____1399 = check_bv env1 x  in
                (match uu____1399 with
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
                let uu____1456 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1592  ->
                          fun uu____1593  ->
                            match (uu____1592, uu____1593) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1791 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1791 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1867 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1867, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1456 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1998 =
                         let uu____2003 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2004 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2003 uu____2004
                          in
                       uu____1998 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2011 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2022 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2033 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2011, uu____2022, uu____2033, env2, e, guard,
                       (let uu___101_2055 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___101_2055.FStar_Syntax_Syntax.p)
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
                    (fun uu____2149  ->
                       match uu____2149 with
                       | (p2,imp) ->
                           let uu____2168 = elaborate_pat env1 p2  in
                           (uu____2168, imp)) pats
                   in
                let uu____2173 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2173 with
                 | (uu____2180,t) ->
                     let uu____2182 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2182 with
                      | (f,uu____2198) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2324::uu____2325) ->
                                let uu____2368 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2368
                            | (uu____2377::uu____2378,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2456  ->
                                        match uu____2456 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2483 =
                                                     let uu____2486 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2486
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2483
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2488 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2488, true)
                                             | uu____2493 ->
                                                 let uu____2496 =
                                                   let uu____2501 =
                                                     let uu____2502 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2502
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2501)
                                                    in
                                                 let uu____2503 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2496 uu____2503)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2577,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2578)) when p_imp ->
                                     let uu____2581 = aux formals' pats'  in
                                     (p2, true) :: uu____2581
                                 | (uu____2598,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2606 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2606
                                        in
                                     let uu____2607 = aux formals' pats2  in
                                     (p3, true) :: uu____2607
                                 | (uu____2624,imp) ->
                                     let uu____2630 =
                                       let uu____2637 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2637)  in
                                     let uu____2640 = aux formals' pats'  in
                                     uu____2630 :: uu____2640)
                             in
                          let uu___102_2655 = p1  in
                          let uu____2658 =
                            let uu____2659 =
                              let uu____2672 = aux f pats1  in
                              (fv, uu____2672)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2659  in
                          {
                            FStar_Syntax_Syntax.v = uu____2658;
                            FStar_Syntax_Syntax.p =
                              (uu___102_2655.FStar_Syntax_Syntax.p)
                          }))
            | uu____2689 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2731 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2731 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2789 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2789 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2815 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2815
                       p3.FStar_Syntax_Syntax.p
                 | uu____2838 -> (b, a, w, arg, guard, p3))
             in
          let uu____2847 = one_pat true env p  in
          match uu____2847 with
          | (b,uu____2877,uu____2878,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____2936,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2938)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2943,uu____2944) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2948 =
                    let uu____2949 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2950 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2949 uu____2950
                     in
                  failwith uu____2948)
               else ();
               (let uu____2953 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2953
                then
                  let uu____2954 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2955 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2954
                    uu____2955
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___103_2959 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___103_2959.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___103_2959.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2963 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2963
                then
                  let uu____2964 =
                    let uu____2965 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2966 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2965 uu____2966
                     in
                  failwith uu____2964
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___104_2970 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___104_2970.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___104_2970.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2972),uu____2973) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2995 =
                  let uu____2996 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2996  in
                if uu____2995
                then
                  let uu____2997 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2997
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3016;
                FStar_Syntax_Syntax.vars = uu____3017;_},args))
              ->
              ((let uu____3056 =
                  let uu____3057 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3057 Prims.op_Negation  in
                if uu____3056
                then
                  let uu____3058 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3058
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3200)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3275) ->
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
                       | ((e2,imp),uu____3312) ->
                           let pat =
                             let uu____3334 = aux argpat e2  in
                             let uu____3335 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3334, uu____3335)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3340 ->
                      let uu____3363 =
                        let uu____3364 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3365 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3364 uu____3365
                         in
                      failwith uu____3363
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3377;
                     FStar_Syntax_Syntax.vars = uu____3378;_},uu____3379);
                FStar_Syntax_Syntax.pos = uu____3380;
                FStar_Syntax_Syntax.vars = uu____3381;_},args))
              ->
              ((let uu____3424 =
                  let uu____3425 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3425 Prims.op_Negation  in
                if uu____3424
                then
                  let uu____3426 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3426
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3568)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3643) ->
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
                       | ((e2,imp),uu____3680) ->
                           let pat =
                             let uu____3702 = aux argpat e2  in
                             let uu____3703 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3702, uu____3703)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3708 ->
                      let uu____3731 =
                        let uu____3732 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3733 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3732 uu____3733
                         in
                      failwith uu____3731
                   in
                match_args [] args argpats))
          | uu____3742 ->
              let uu____3747 =
                let uu____3748 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3749 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3750 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3748 uu____3749 uu____3750
                 in
              failwith uu____3747
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
    let pat_as_arg uu____3793 =
      match uu____3793 with
      | (p,i) ->
          let uu____3810 = decorated_pattern_as_term p  in
          (match uu____3810 with
           | (vars,te) ->
               let uu____3833 =
                 let uu____3838 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3838)  in
               (vars, uu____3833))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3852 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3852)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3856 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3856)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3860 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3860)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3881 =
          let uu____3896 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3896 FStar_List.unzip  in
        (match uu____3881 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4006 =
               let uu____4007 =
                 let uu____4008 =
                   let uu____4023 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4023, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4008  in
               mk1 uu____4007  in
             (vars1, uu____4006))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4055,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4065,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4079 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4105)::[] -> wp
      | uu____4122 ->
          let uu____4131 =
            let uu____4132 =
              let uu____4133 =
                FStar_List.map
                  (fun uu____4143  ->
                     match uu____4143 with
                     | (x,uu____4149) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4133 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4132
             in
          failwith uu____4131
       in
    let uu____4154 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4154, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4174 = destruct_comp c  in
        match uu____4174 with
        | (u,uu____4182,wp) ->
            let uu____4184 =
              let uu____4193 =
                let uu____4194 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4194  in
              [uu____4193]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4184;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4210 =
          let uu____4217 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4218 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4217 uu____4218  in
        match uu____4210 with | (m,uu____4220,uu____4221) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4237 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4237
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
        let uu____4280 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4280 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4317 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4317 with
             | (a,kwp) ->
                 let uu____4348 = destruct_comp m1  in
                 let uu____4355 = destruct_comp m2  in
                 ((md, a, kwp), uu____4348, uu____4355))
  
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
            let uu____4435 =
              let uu____4436 =
                let uu____4445 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4445]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4436;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4435
  
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
          let uu____4499 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4499
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
      let uu____4511 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4511
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4514  ->
           let uu____4515 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4515)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4521 =
      let uu____4522 = FStar_Syntax_Subst.compress t  in
      uu____4522.FStar_Syntax_Syntax.n  in
    match uu____4521 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4525 -> true
    | uu____4538 -> false
  
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
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4593 =
                let uu____4594 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4594  in
              if uu____4593
              then f
              else (let uu____4596 = reason1 ()  in label uu____4596 r f)
  
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
            let uu___105_4613 = g  in
            let uu____4614 =
              let uu____4615 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4615  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4614;
              FStar_TypeChecker_Env.deferred =
                (uu___105_4613.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___105_4613.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___105_4613.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4635 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4635
        then c
        else
          (let uu____4637 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4637
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4686 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4686]  in
                       let us =
                         let uu____4690 =
                           let uu____4693 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4693]  in
                         u_res :: uu____4690  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4697 =
                         let uu____4702 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4703 =
                           let uu____4704 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4705 =
                             let uu____4708 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4709 =
                               let uu____4712 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4712]  in
                             uu____4708 :: uu____4709  in
                           uu____4704 :: uu____4705  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4702 uu____4703
                          in
                       uu____4697 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4716 = destruct_comp c1  in
              match uu____4716 with
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
          (fun uu____4749  ->
             let uu____4750 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4750)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___78_4759  ->
            match uu___78_4759 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4760 -> false))
  
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
                (let uu____4782 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4782))
               &&
               (let uu____4789 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4789 with
                | (head1,uu____4803) ->
                    let uu____4820 =
                      let uu____4821 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4821.FStar_Syntax_Syntax.n  in
                    (match uu____4820 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4825 =
                           let uu____4826 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4826
                            in
                         Prims.op_Negation uu____4825
                     | uu____4827 -> true)))
              &&
              (let uu____4829 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4829)
  
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
            let uu____4855 =
              let uu____4856 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4856  in
            if uu____4855
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4858 = FStar_Syntax_Util.is_unit t  in
               if uu____4858
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
                    let uu____4864 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4864
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4866 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4866 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4874 =
                             let uu____4875 =
                               let uu____4880 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4881 =
                                 let uu____4882 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4883 =
                                   let uu____4886 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4886]  in
                                 uu____4882 :: uu____4883  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4880
                                 uu____4881
                                in
                             uu____4875 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4874)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4890 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4890
           then
             let uu____4891 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4892 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4893 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4891 uu____4892 uu____4893
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4906 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___79_4910  ->
              match uu___79_4910 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4911 -> false))
       in
    if uu____4906
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___80_4920  ->
              match uu___80_4920 with
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
        let uu____4939 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4939
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4942 = destruct_comp c1  in
           match uu____4942 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4956 =
                   let uu____4961 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4962 =
                     let uu____4963 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4964 =
                       let uu____4967 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4968 =
                         let uu____4971 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4971]  in
                       uu____4967 :: uu____4968  in
                     uu____4963 :: uu____4964  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4961 uu____4962  in
                 uu____4956 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4974 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4974)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4997 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4999 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4999
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5002 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5002 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
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
               let uu____5045 = destruct_comp c1  in
               match uu____5045 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5059 =
                       let uu____5064 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5065 =
                         let uu____5066 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5067 =
                           let uu____5070 =
                             let uu____5071 =
                               let uu____5072 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5072 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5071
                              in
                           let uu____5073 =
                             let uu____5076 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5076]  in
                           uu____5070 :: uu____5073  in
                         uu____5066 :: uu____5067  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5064 uu____5065
                        in
                     uu____5059 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
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
            let uu____5121 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5121
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5130 =
                   let uu____5137 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5137
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5130 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5157 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___81_5165  ->
                               match uu___81_5165 with
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
                               | uu____5168 -> []))
                        in
                     FStar_List.append flags1 uu____5157
                  in
               let strengthen uu____5174 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5178 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5178 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5181 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5181
                          then
                            let uu____5182 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5183 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5182 uu____5183
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5185 =
                 let uu____5186 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5186
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5185,
                 (let uu___106_5188 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___106_5188.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___106_5188.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___106_5188.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___82_5195  ->
            match uu___82_5195 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5196 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5221 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5221
          then e
          else
            (let uu____5223 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5225 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5225)
                in
             if uu____5223
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
          fun uu____5273  ->
            match uu____5273 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5293 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5293 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5301 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5301
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5308 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5308
                       then
                         let uu____5311 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5311
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5315 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5315
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5320 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5320
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5324 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5324
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5333 =
                  let uu____5334 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5334
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
                       (fun uu____5348  ->
                          let uu____5349 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5350 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5352 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5349 uu____5350 uu____5352);
                     (let aux uu____5366 =
                        let uu____5367 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5367
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5388 ->
                              let uu____5389 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5389
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5408 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5408
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5479 =
                              let uu____5484 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5484, reason)  in
                            FStar_Util.Inl uu____5479
                        | uu____5491 -> aux ()  in
                      let try_simplify uu____5515 =
                        let rec maybe_close t x c =
                          let uu____5532 =
                            let uu____5533 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5533.FStar_Syntax_Syntax.n  in
                          match uu____5532 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5537) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5543 -> c  in
                        let uu____5544 =
                          let uu____5545 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5545  in
                        if uu____5544
                        then
                          let uu____5556 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____5556
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5570 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5570))
                        else
                          (let uu____5580 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5580
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5590 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5590
                              then
                                let uu____5599 =
                                  let uu____5604 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5604, "both gtot")  in
                                FStar_Util.Inl uu____5599
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5628 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5630 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____5630)
                                        in
                                     if uu____5628
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___107_5641 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___107_5641.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___107_5641.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____5642 =
                                         let uu____5647 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____5647, "c1 Tot")  in
                                       FStar_Util.Inl uu____5642
                                     else aux ()
                                 | uu____5653 -> aux ())))
                         in
                      let uu____5662 = try_simplify ()  in
                      match uu____5662 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5682  ->
                                let uu____5683 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5683);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5692  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5713 = lift_and_destruct env c11 c21
                                 in
                              match uu____5713 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5770 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5770]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5772 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5772]
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
                                    let uu____5787 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5788 =
                                      let uu____5791 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5792 =
                                        let uu____5795 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5796 =
                                          let uu____5799 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5800 =
                                            let uu____5803 =
                                              let uu____5804 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5804
                                               in
                                            [uu____5803]  in
                                          uu____5799 :: uu____5800  in
                                        uu____5795 :: uu____5796  in
                                      uu____5791 :: uu____5792  in
                                    uu____5787 :: uu____5788  in
                                  let wp =
                                    let uu____5808 =
                                      let uu____5813 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5813 wp_args
                                       in
                                    uu____5808 FStar_Pervasives_Native.None
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
                              let uu____5838 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5838 with
                              | (m,uu____5846,lift2) ->
                                  let c23 =
                                    let uu____5849 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5849
                                     in
                                  let uu____5850 = destruct_comp c12  in
                                  (match uu____5850 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5864 =
                                           let uu____5869 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____5870 =
                                             let uu____5871 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____5872 =
                                               let uu____5875 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____5875]  in
                                             uu____5871 :: uu____5872  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5869 uu____5870
                                            in
                                         uu____5864
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
                            let uu____5882 = destruct_comp c1_typ  in
                            match uu____5882 with
                            | (u_res_t1,res_t1,uu____5891) ->
                                let uu____5892 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____5892
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____5895 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____5895
                                   then
                                     (debug1
                                        (fun uu____5903  ->
                                           let uu____5904 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____5905 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5904 uu____5905);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5908 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5910 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____5910)
                                         in
                                      if uu____5908
                                      then
                                        let e1' =
                                          let uu____5932 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____5932
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____5943  ->
                                              let uu____5944 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____5945 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5944 uu____5945);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5957  ->
                                              let uu____5958 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5959 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5958 uu____5959);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____5962 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5962
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
      | uu____5978 -> g2
  
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
            (let uu____6000 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6000)
           in
        let flags1 =
          if should_return1
          then
            let uu____6006 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6006
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6016 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6020 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6020
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6022 =
              let uu____6023 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6023  in
            (if uu____6022
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___108_6026 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___108_6026.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___108_6026.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___108_6026.FStar_Syntax_Syntax.effect_args);
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
               let uu____6037 =
                 let uu____6040 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6040
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6037
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6045 =
               let uu____6046 =
                 let uu____6047 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6047
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6046  in
             FStar_Syntax_Util.comp_set_flags uu____6045 flags1)
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
            fun uu____6082  ->
              match uu____6082 with
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
                    let uu____6094 =
                      ((let uu____6097 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6097) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6094
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6111 =
        let uu____6112 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6112  in
      FStar_Syntax_Syntax.fvar uu____6111 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____6178  ->
                 match uu____6178 with
                 | (uu____6191,eff_label,uu____6193,uu____6194) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6205 =
          let uu____6212 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6246  ->
                    match uu____6246 with
                    | (uu____6259,uu____6260,flags1,uu____6262) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___83_6276  ->
                                match uu___83_6276 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6277 -> false))))
             in
          if uu____6212
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6205 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6300 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6302 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6302
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6332 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6333 =
                     let uu____6338 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6339 =
                       let uu____6340 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6341 =
                         let uu____6344 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6345 =
                           let uu____6348 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6349 =
                             let uu____6352 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6352]  in
                           uu____6348 :: uu____6349  in
                         uu____6344 :: uu____6345  in
                       uu____6340 :: uu____6341  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6338 uu____6339  in
                   uu____6333 FStar_Pervasives_Native.None uu____6332  in
                 let default_case =
                   let post_k =
                     let uu____6359 =
                       let uu____6366 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6366]  in
                     let uu____6367 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6359 uu____6367  in
                   let kwp =
                     let uu____6373 =
                       let uu____6380 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6380]  in
                     let uu____6381 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6373 uu____6381  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6386 =
                       let uu____6387 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6387]  in
                     let uu____6388 =
                       let uu____6389 =
                         let uu____6394 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6394
                          in
                       let uu____6395 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6389 uu____6395  in
                     FStar_Syntax_Util.abs uu____6386 uu____6388
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
                   let uu____6415 =
                     should_not_inline_whole_match ||
                       (let uu____6417 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6417)
                      in
                   if uu____6415 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6450  ->
                        fun celse  ->
                          match uu____6450 with
                          | (g,eff_label,uu____6466,cthen) ->
                              let uu____6478 =
                                let uu____6503 =
                                  let uu____6504 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6504
                                   in
                                lift_and_destruct env uu____6503 celse  in
                              (match uu____6478 with
                               | ((md,uu____6506,uu____6507),(uu____6508,uu____6509,wp_then),
                                  (uu____6511,uu____6512,wp_else)) ->
                                   let uu____6532 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6532 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6546::[] -> comp
                 | uu____6586 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6604 = destruct_comp comp1  in
                     (match uu____6604 with
                      | (uu____6611,uu____6612,wp) ->
                          let wp1 =
                            let uu____6617 =
                              let uu____6622 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6623 =
                                let uu____6624 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6625 =
                                  let uu____6628 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6628]  in
                                uu____6624 :: uu____6625  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6622
                                uu____6623
                               in
                            uu____6617 FStar_Pervasives_Native.None
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
          let uu____6663 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6663 with
          | FStar_Pervasives_Native.None  ->
              let uu____6672 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6677 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6672 uu____6677
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
            let uu____6720 =
              let uu____6721 = FStar_Syntax_Subst.compress t2  in
              uu____6721.FStar_Syntax_Syntax.n  in
            match uu____6720 with
            | FStar_Syntax_Syntax.Tm_type uu____6724 -> true
            | uu____6725 -> false  in
          let uu____6726 =
            let uu____6727 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6727.FStar_Syntax_Syntax.n  in
          match uu____6726 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6735 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____6745 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____6745
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6747 =
                  let uu____6748 =
                    let uu____6749 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6749
                     in
                  (FStar_Pervasives_Native.None, uu____6748)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6747
                 in
              let e1 =
                let uu____6759 =
                  let uu____6764 =
                    let uu____6765 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6765]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6764  in
                uu____6759 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6770 -> (e, lc)
  
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
              (let uu____6807 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6807 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6830 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6852 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6852, false)
            else
              (let uu____6858 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6858, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6869) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6878 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6878 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___109_6892 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___109_6892.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___109_6892.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___109_6892.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6897 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6897 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let uu____6904 =
                     FStar_Ident.lid_equals
                       env.FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid
                      in
                   if uu____6904
                   then
                     (e,
                       (let uu___110_6912 = lc  in
                        {
                          FStar_Syntax_Syntax.eff_name =
                            (uu___110_6912.FStar_Syntax_Syntax.eff_name);
                          FStar_Syntax_Syntax.res_typ = t;
                          FStar_Syntax_Syntax.cflags =
                            (uu___110_6912.FStar_Syntax_Syntax.cflags);
                          FStar_Syntax_Syntax.comp_thunk =
                            (uu___110_6912.FStar_Syntax_Syntax.comp_thunk)
                        }), g)
                   else
                     (let uu____6914 =
                        FStar_Syntax_Util.set_result_typ_lc lc t  in
                      (e, uu____6914, g))
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___111_6917 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___111_6917.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___111_6917.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___111_6917.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6923 =
                     let uu____6924 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6924
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6927 =
                          let uu____6928 = FStar_Syntax_Subst.compress f1  in
                          uu____6928.FStar_Syntax_Syntax.n  in
                        match uu____6927 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6931,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6933;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6934;_},uu____6935)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___112_6957 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___112_6957.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___112_6957.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___112_6957.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6958 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____6961 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6961
                              then
                                let uu____6962 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6963 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6964 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6965 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6962 uu____6963 uu____6964 uu____6965
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
                                  let uu____6978 =
                                    let uu____6983 =
                                      let uu____6984 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____6984]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6983
                                     in
                                  uu____6978 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____6988 =
                                let uu____6993 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7010 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7011 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7012 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____6993 uu____7010
                                  e uu____7011 uu____7012
                                 in
                              match uu____6988 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___113_7016 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___113_7016.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___113_7016.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7018 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7018
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7023 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7023
                                    then
                                      let uu____7024 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7024
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___84_7034  ->
                             match uu___84_7034 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7037 -> []))
                      in
                   let lc1 =
                     let uu____7039 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7039 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___114_7041 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___114_7041.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___114_7041.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___114_7041.FStar_TypeChecker_Env.implicits)
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
        let uu____7072 =
          let uu____7073 =
            let uu____7078 =
              let uu____7079 =
                let uu____7080 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7080  in
              [uu____7079]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7078  in
          uu____7073 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7072  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7089 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7089
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7107 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7122 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7138 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7138
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7152)::(ens,uu____7154)::uu____7155 ->
                    let uu____7184 =
                      let uu____7187 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7187  in
                    let uu____7188 =
                      let uu____7189 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7189  in
                    (uu____7184, uu____7188)
                | uu____7192 ->
                    let uu____7201 =
                      let uu____7206 =
                        let uu____7207 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7207
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7206)
                       in
                    FStar_Errors.raise_error uu____7201
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7223)::uu____7224 ->
                    let uu____7243 =
                      let uu____7248 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7248
                       in
                    (match uu____7243 with
                     | (us_r,uu____7280) ->
                         let uu____7281 =
                           let uu____7286 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7286
                            in
                         (match uu____7281 with
                          | (us_e,uu____7318) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____7321 =
                                  let uu____7322 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7322
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7321
                                  us_r
                                 in
                              let as_ens =
                                let uu____7324 =
                                  let uu____7325 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7325
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7324
                                  us_e
                                 in
                              let req =
                                let uu____7329 =
                                  let uu____7334 =
                                    let uu____7335 =
                                      let uu____7346 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7346]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7335
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7334
                                   in
                                uu____7329 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____7364 =
                                  let uu____7369 =
                                    let uu____7370 =
                                      let uu____7381 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7381]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7370
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7369
                                   in
                                uu____7364 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____7396 =
                                let uu____7399 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____7399  in
                              let uu____7400 =
                                let uu____7401 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____7401  in
                              (uu____7396, uu____7400)))
                | uu____7404 -> failwith "Impossible"))
  
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
      (let uu____7434 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____7434
       then
         let uu____7435 = FStar_Syntax_Print.term_to_string tm  in
         let uu____7436 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7435 uu____7436
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
        (let uu____7460 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____7460
         then
           let uu____7461 = FStar_Syntax_Print.term_to_string tm  in
           let uu____7462 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7461
             uu____7462
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____7469 =
      let uu____7470 =
        let uu____7471 = FStar_Syntax_Subst.compress t  in
        uu____7471.FStar_Syntax_Syntax.n  in
      match uu____7470 with
      | FStar_Syntax_Syntax.Tm_app uu____7474 -> false
      | uu____7489 -> true  in
    if uu____7469
    then t
    else
      (let uu____7491 = FStar_Syntax_Util.head_and_args t  in
       match uu____7491 with
       | (head1,args) ->
           let uu____7528 =
             let uu____7529 =
               let uu____7530 = FStar_Syntax_Subst.compress head1  in
               uu____7530.FStar_Syntax_Syntax.n  in
             match uu____7529 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7533 -> false  in
           if uu____7528
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7555 ->
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
             let uu____7600 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7600 with
             | (formals,uu____7614) ->
                 let n_implicits =
                   let uu____7632 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7708  ->
                             match uu____7708 with
                             | (uu____7715,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7632 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7848 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7848 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7872 =
                     let uu____7877 =
                       let uu____7878 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7885 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7886 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7878 uu____7885 uu____7886
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7877)
                      in
                   let uu____7893 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7872 uu____7893
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___85_7916 =
             match uu___85_7916 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7946 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7946 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8061) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8104,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8137 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8137 with
                           | (v1,uu____8177,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____8194 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____8194 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8287 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8287)))
                      | (uu____8314,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____8360 =
                      let uu____8387 = inst_n_binders t  in
                      aux [] uu____8387 bs1  in
                    (match uu____8360 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8458) -> (e, torig, guard)
                          | (uu____8489,[]) when
                              let uu____8520 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8520 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8521 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8553 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8568 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8578 =
      let uu____8581 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8581
        (FStar_List.map
           (fun u  ->
              let uu____8591 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8591 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8578 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8612 = FStar_Util.set_is_empty x  in
      if uu____8612
      then []
      else
        (let s =
           let uu____8619 =
             let uu____8622 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8622  in
           FStar_All.pipe_right uu____8619 FStar_Util.set_elements  in
         (let uu____8630 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____8630
          then
            let uu____8631 =
              let uu____8632 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____8632  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8631
          else ());
         (let r =
            let uu____8639 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____8639  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____8654 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8654
                     then
                       let uu____8655 =
                         let uu____8656 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8656
                          in
                       let uu____8657 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8658 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8655 uu____8657 uu____8658
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
        let uu____8684 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____8684 FStar_Util.set_elements  in
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
        | ([],uu____8722) -> generalized_univ_names
        | (uu____8729,[]) -> explicit_univ_names
        | uu____8736 ->
            let uu____8745 =
              let uu____8750 =
                let uu____8751 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8751
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8750)
               in
            FStar_Errors.raise_error uu____8745 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____8769 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____8769
       then
         let uu____8770 = FStar_Syntax_Print.term_to_string t  in
         let uu____8771 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____8770 uu____8771
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____8777 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8777
        then
          let uu____8778 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____8778
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____8784 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____8784
         then
           let uu____8785 = FStar_Syntax_Print.term_to_string t  in
           let uu____8786 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____8785 uu____8786
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
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
        let uu____8862 =
          let uu____8863 =
            FStar_Util.for_all
              (fun uu____8876  ->
                 match uu____8876 with
                 | (uu____8885,uu____8886,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8863  in
        if uu____8862
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8934 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8934
              then
                let uu____8935 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8935
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____8939 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8939
               then
                 let uu____8940 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8940
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9003 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9003 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9135 =
             match uu____9135 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9201 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9201
                   then
                     let uu____9202 =
                       let uu____9203 =
                         let uu____9206 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9206
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9203
                         (FStar_String.concat ", ")
                        in
                     let uu____9233 =
                       let uu____9234 =
                         let uu____9237 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9237
                           (FStar_List.map
                              (fun uu____9265  ->
                                 match uu____9265 with
                                 | (u,t2) ->
                                     let uu____9272 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____9273 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____9272 uu____9273))
                          in
                       FStar_All.pipe_right uu____9234
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9202
                       uu____9233
                   else ());
                  (let univs2 =
                     let uu____9280 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____9303  ->
                            match uu____9303 with
                            | (uu____9312,t2) ->
                                let uu____9314 = FStar_Syntax_Free.univs t2
                                   in
                                FStar_Util.set_union univs2 uu____9314)
                       univs1 uu____9280
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____9337 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____9337
                    then
                      let uu____9338 =
                        let uu____9339 =
                          let uu____9342 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____9342
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____9339
                          (FStar_String.concat ", ")
                         in
                      let uu____9369 =
                        let uu____9370 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____9402  ->
                                  match uu____9402 with
                                  | (u,t2) ->
                                      let uu____9409 =
                                        FStar_Syntax_Print.uvar_to_string u
                                         in
                                      let uu____9410 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2
                                         in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____9409 uu____9410))
                           in
                        FStar_All.pipe_right uu____9370
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9338
                        uu____9369
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____9440 =
             let uu____9473 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____9473  in
           match uu____9440 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9597 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9597
                 then ()
                 else
                   (let uu____9599 = lec_hd  in
                    match uu____9599 with
                    | (lb1,uu____9607,uu____9608) ->
                        let uu____9609 = lec2  in
                        (match uu____9609 with
                         | (lb2,uu____9617,uu____9618) ->
                             let msg =
                               let uu____9620 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9621 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9620 uu____9621
                                in
                             let uu____9622 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9622))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9743  ->
                           match uu____9743 with
                           | (u,uu____9751) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9773  ->
                                       match uu____9773 with
                                       | (u',uu____9781) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9786 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9786
                 then ()
                 else
                   (let uu____9788 = lec_hd  in
                    match uu____9788 with
                    | (lb1,uu____9796,uu____9797) ->
                        let uu____9798 = lec2  in
                        (match uu____9798 with
                         | (lb2,uu____9806,uu____9807) ->
                             let msg =
                               let uu____9809 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9810 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9809 uu____9810
                                in
                             let uu____9811 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9811))
                  in
               let lecs1 =
                 let uu____9821 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9880 = univs_and_uvars_of_lec this_lec  in
                        match uu____9880 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9821 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10037 = lec_hd  in
                   match uu____10037 with
                   | (lbname,e,c) ->
                       let uu____10047 =
                         let uu____10052 =
                           let uu____10053 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10054 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10055 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10053 uu____10054 uu____10055
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10052)
                          in
                       let uu____10056 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10047 uu____10056
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____10086  ->
                         match uu____10086 with
                         | (u,k) ->
                             let uu____10099 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____10099 with
                              | FStar_Pervasives_Native.Some uu____10108 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____10115 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____10119 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____10119 with
                                   | (bs,kres) ->
                                       ((let uu____10157 =
                                           let uu____10158 =
                                             let uu____10161 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____10161
                                              in
                                           uu____10158.FStar_Syntax_Syntax.n
                                            in
                                         match uu____10157 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____10162 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____10166 =
                                               let uu____10167 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____10167
                                                in
                                             if uu____10166
                                             then fail1 kres
                                             else ()
                                         | uu____10169 -> fail1 kres);
                                        (let a =
                                           let uu____10171 =
                                             let uu____10174 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_19  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_19) uu____10174
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____10171 kres
                                            in
                                         let t =
                                           let uu____10178 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Util.abs bs
                                             uu____10178
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
                      (fun uu____10297  ->
                         match uu____10297 with
                         | (lbname,e,c) ->
                             let uu____10343 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10412 ->
                                   let uu____10427 = (e, c)  in
                                   (match uu____10427 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
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
                                                (fun uu____10464  ->
                                                   match uu____10464 with
                                                   | (x,uu____10472) ->
                                                       let uu____10477 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10477)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10491 =
                                                let uu____10492 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10492
                                                 in
                                              if uu____10491
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
                                          let uu____10500 =
                                            let uu____10501 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10501.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10500 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10524 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10524 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10539 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10541 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10541, gen_tvars))
                                in
                             (match uu____10343 with
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
        (let uu____10695 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10695
         then
           let uu____10696 =
             let uu____10697 =
               FStar_List.map
                 (fun uu____10710  ->
                    match uu____10710 with
                    | (lb,uu____10718,uu____10719) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10697 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10696
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10740  ->
                match uu____10740 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10769 = gen env is_rec lecs  in
           match uu____10769 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10868  ->
                       match uu____10868 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10930 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10930
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10974  ->
                           match uu____10974 with
                           | (l,us,e,c,gvs) ->
                               let uu____11008 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11009 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11010 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11011 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11012 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11008 uu____11009 uu____11010
                                 uu____11011 uu____11012))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11053  ->
                match uu____11053 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11097 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11097, t, c, gvs)) univnames_lecs
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
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____11154 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11154 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11160 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11160)
             in
          let is_var e1 =
            let uu____11169 =
              let uu____11170 = FStar_Syntax_Subst.compress e1  in
              uu____11170.FStar_Syntax_Syntax.n  in
            match uu____11169 with
            | FStar_Syntax_Syntax.Tm_name uu____11173 -> true
            | uu____11174 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___115_11194 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___115_11194.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___115_11194.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11195 -> e2  in
          let env2 =
            let uu___116_11197 = env1  in
            let uu____11198 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_11197.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_11197.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_11197.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_11197.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_11197.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_11197.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_11197.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_11197.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_11197.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_11197.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_11197.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_11197.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_11197.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___116_11197.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_11197.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11198;
              FStar_TypeChecker_Env.is_iface =
                (uu___116_11197.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_11197.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_11197.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_11197.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___116_11197.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___116_11197.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___116_11197.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___116_11197.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_11197.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___116_11197.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_11197.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___116_11197.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___116_11197.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___116_11197.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___116_11197.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___116_11197.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___116_11197.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___116_11197.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___116_11197.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___116_11197.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___116_11197.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11199 = check1 env2 t1 t2  in
          match uu____11199 with
          | FStar_Pervasives_Native.None  ->
              let uu____11206 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11211 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11206 uu____11211
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11218 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11218
                then
                  let uu____11219 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11219
                else ());
               (let uu____11221 = decorate e t2  in (uu____11221, g)))
  
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
        let uu____11257 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11257
        then
          let uu____11262 = discharge g1  in
          let uu____11263 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11262, uu____11263)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11270 =
               let uu____11271 =
                 let uu____11272 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11272 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11271
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11270
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11274 = destruct_comp c1  in
           match uu____11274 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11291 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11292 =
                   let uu____11297 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11298 =
                     let uu____11299 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11300 =
                       let uu____11303 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11303]  in
                     uu____11299 :: uu____11300  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11297 uu____11298  in
                 uu____11292 FStar_Pervasives_Native.None uu____11291  in
               ((let uu____11307 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11307
                 then
                   let uu____11308 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11308
                 else ());
                (let g2 =
                   let uu____11311 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11311  in
                 let uu____11312 = discharge g2  in
                 let uu____11313 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11312, uu____11313))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___86_11345 =
        match uu___86_11345 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11353)::[] -> f fst1
        | uu____11370 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11377 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11377
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11388 =
          let uu____11391 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11391  in
        FStar_All.pipe_right uu____11388
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11406 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11406
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___87_11424 =
        match uu___87_11424 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11432)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11451)::[] ->
            let uu____11480 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11480
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11485 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11496 =
          let uu____11504 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11504)  in
        let uu____11512 =
          let uu____11522 =
            let uu____11530 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____11530)  in
          let uu____11538 =
            let uu____11548 =
              let uu____11556 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____11556)  in
            let uu____11564 =
              let uu____11574 =
                let uu____11582 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____11582)  in
              let uu____11590 =
                let uu____11600 =
                  let uu____11608 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____11608)  in
                [uu____11600; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____11574 :: uu____11590  in
            uu____11548 :: uu____11564  in
          uu____11522 :: uu____11538  in
        uu____11496 :: uu____11512  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11670 =
            FStar_Util.find_map table
              (fun uu____11685  ->
                 match uu____11685 with
                 | (x,mk1) ->
                     let uu____11702 = FStar_Ident.lid_equals x lid  in
                     if uu____11702
                     then
                       let uu____11705 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11705
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11670 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11708 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11714 =
      let uu____11715 = FStar_Syntax_Util.un_uinst l  in
      uu____11715.FStar_Syntax_Syntax.n  in
    match uu____11714 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11719 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11749)::uu____11750 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11761 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11768,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11769))::uu____11770 -> bs
      | uu____11787 ->
          let uu____11788 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11788 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11792 =
                 let uu____11793 = FStar_Syntax_Subst.compress t  in
                 uu____11793.FStar_Syntax_Syntax.n  in
               (match uu____11792 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11797) ->
                    let uu____11814 =
                      FStar_Util.prefix_until
                        (fun uu___88_11854  ->
                           match uu___88_11854 with
                           | (uu____11861,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11862)) ->
                               false
                           | uu____11865 -> true) bs'
                       in
                    (match uu____11814 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11900,uu____11901) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11973,uu____11974) ->
                         let uu____12047 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12065  ->
                                   match uu____12065 with
                                   | (x,uu____12073) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12047
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12120  ->
                                     match uu____12120 with
                                     | (x,i) ->
                                         let uu____12139 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12139, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12149 -> bs))
  
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
            let uu____12177 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12177
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
          let uu____12200 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12200
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> unit) =
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
        (let uu____12231 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12231
         then
           ((let uu____12233 = FStar_Ident.text_of_lid lident  in
             d uu____12233);
            (let uu____12234 = FStar_Ident.text_of_lid lident  in
             let uu____12235 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12234 uu____12235))
         else ());
        (let fv =
           let uu____12238 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12238
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____12248 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___117_12254 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___117_12254.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___117_12254.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___117_12254.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___117_12254.FStar_Syntax_Syntax.sigattrs)
           }), uu____12248))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___89_12270 =
        match uu___89_12270 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12271 -> false  in
      let reducibility uu___90_12277 =
        match uu___90_12277 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12278 -> false  in
      let assumption uu___91_12284 =
        match uu___91_12284 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12285 -> false  in
      let reification uu___92_12291 =
        match uu___92_12291 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12292 -> true
        | uu____12293 -> false  in
      let inferred uu___93_12299 =
        match uu___93_12299 with
        | FStar_Syntax_Syntax.Discriminator uu____12300 -> true
        | FStar_Syntax_Syntax.Projector uu____12301 -> true
        | FStar_Syntax_Syntax.RecordType uu____12306 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12315 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12324 -> false  in
      let has_eq uu___94_12330 =
        match uu___94_12330 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12331 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
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
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
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
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____12395 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12400 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12404 =
        let uu____12405 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___95_12409  ->
                  match uu___95_12409 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12410 -> false))
           in
        FStar_All.pipe_right uu____12405 Prims.op_Negation  in
      if uu____12404
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12425 =
            let uu____12430 =
              let uu____12431 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12431 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12430)  in
          FStar_Errors.raise_error uu____12425 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12443 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12447 =
            let uu____12448 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12448  in
          if uu____12447 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12453),uu____12454) ->
              ((let uu____12470 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12470
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12474 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12474
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12480 ->
              let uu____12489 =
                let uu____12490 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12490  in
              if uu____12489 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12496 ->
              let uu____12503 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12503 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12507 ->
              let uu____12514 =
                let uu____12515 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12515  in
              if uu____12514 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12521 ->
              let uu____12522 =
                let uu____12523 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12523  in
              if uu____12522 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12529 ->
              let uu____12530 =
                let uu____12531 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12531  in
              if uu____12530 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12537 ->
              let uu____12550 =
                let uu____12551 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____12551  in
              if uu____12550 then err'1 () else ()
          | uu____12557 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____12591 =
          let uu____12592 = FStar_Syntax_Subst.compress t1  in
          uu____12592.FStar_Syntax_Syntax.n  in
        match uu____12591 with
        | FStar_Syntax_Syntax.Tm_type uu____12595 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____12598 =
                 let uu____12603 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____12603
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____12598
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____12621 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____12621
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____12638 =
                                 let uu____12639 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____12639.FStar_Syntax_Syntax.n  in
                               match uu____12638 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____12643 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____12644 ->
            let uu____12657 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____12657 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____12683 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____12683
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____12685;
               FStar_Syntax_Syntax.index = uu____12686;
               FStar_Syntax_Syntax.sort = t2;_},uu____12688)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12696,uu____12697) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____12739::[]) ->
            let uu____12770 =
              let uu____12771 = FStar_Syntax_Util.un_uinst head1  in
              uu____12771.FStar_Syntax_Syntax.n  in
            (match uu____12770 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____12775 -> false)
        | uu____12776 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____12784 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____12784
         then
           let uu____12785 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____12785
         else ());
        res
       in aux g t
  